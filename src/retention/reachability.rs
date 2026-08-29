use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::dependency_graph::{DependencyGraph, DependencyKind, GraphNode, ObservationSite};
use crate::source::{CfgState, SourceInventory, SourceUnitId, WrittenUnitKind};

use super::{RetentionError, SourceSiteOwnerIndex, is_compiler_dependency};

struct IndexedCompilerEdge {
    from: GraphNode,
    to: GraphNode,
    site_unconditional: bool,
    target_component: Option<usize>,
}

struct IndexedSourceSite {
    owners: Vec<SourceUnitId>,
    edges: Vec<usize>,
}

struct ExpansionComponent {
    source_units: Vec<SourceUnitId>,
    parents: Vec<usize>,
    children: Vec<usize>,
    target_edges: Vec<usize>,
}

/// Immutable indexes shared by the semantic and compiler retention closures.
///
/// Expansion parent relations are collapsed into SCCs. This preserves the
/// greatest-fixed-point behavior of `expansion_source_survival`: a source-free
/// parent cycle survives as one component, while one missing written gate
/// blocks the whole component and every dependent child.
pub(super) struct CompilerReachabilityIndex {
    edges: Vec<IndexedCompilerEdge>,
    edges_by_from: BTreeMap<GraphNode, Vec<usize>>,
    source_sites: Vec<IndexedSourceSite>,
    sites_by_source: Vec<Vec<usize>>,
    components: Vec<ExpansionComponent>,
    components_by_source: Vec<Vec<usize>>,
}

impl CompilerReachabilityIndex {
    pub(super) fn new(
        source: &SourceInventory,
        source_sites_index: &SourceSiteOwnerIndex,
        graph: &DependencyGraph,
        delegated_macro_expansions: &BTreeSet<crate::dependency_graph::ExpansionId>,
    ) -> Result<Self, RetentionError> {
        let (component_by_expansion, mut components) = expansion_components(source, graph)?;
        let mut edges = Vec::new();
        let mut edges_by_from = BTreeMap::<GraphNode, Vec<usize>>::new();
        let mut source_sites = Vec::<IndexedSourceSite>::new();
        let mut source_site_ids = BTreeMap::new();
        let mut sites_by_source = vec![Vec::new(); source.units.len()];

        for edge in &graph.edges {
            // A refined child is reached through its validated materialization
            // group, and a directly empty child has no output to retain. Keeping
            // either ordinary ExpansionUse would bypass those facts. Direct
            // invocations and children without precise source coverage are not
            // delegated.
            if !is_compiler_dependency(&edge.kind)
                || edge.kind == DependencyKind::ExpansionUse
                    && matches!(
                        edge.to,
                        GraphNode::Expansion(expansion)
                            if delegated_macro_expansions.contains(&expansion)
                    )
            {
                continue;
            }

            let from_definition = matches!(edge.from, GraphNode::Definition(_));
            let site_unconditional = edge.sites.is_empty()
                || !from_definition
                || edge
                    .sites
                    .iter()
                    .any(|site| !matches!(site, ObservationSite::Source(_)));
            let mut edge_source_sites = Vec::new();
            if !site_unconditional {
                for site in &edge.sites {
                    let ObservationSite::Source(range) = site else {
                        unreachable!("conditional compiler edge sites are source ranges");
                    };
                    let site_id = if let Some(&site_id) = source_site_ids.get(range) {
                        site_id
                    } else {
                        let mut owners = source_sites_index.owners(*range)?;
                        owners.sort_unstable();
                        owners.dedup();
                        if owners.is_empty()
                            || owners.iter().any(|owner| {
                                source
                                    .units
                                    .get(owner.0 as usize)
                                    .is_none_or(|unit| unit.id != *owner)
                            })
                        {
                            return Err(RetentionError::InvalidGraph);
                        }
                        let site_id = source_sites.len();
                        for owner in &owners {
                            sites_by_source[owner.0 as usize].push(site_id);
                        }
                        source_sites.push(IndexedSourceSite {
                            owners,
                            edges: Vec::new(),
                        });
                        source_site_ids.insert(*range, site_id);
                        site_id
                    };
                    edge_source_sites.push(site_id);
                }
            }
            edge_source_sites.sort_unstable();
            edge_source_sites.dedup();

            let target_component = match (&edge.kind, edge.to) {
                (
                    DependencyKind::ExpansionUse | DependencyKind::GeneratedBy,
                    GraphNode::Expansion(expansion),
                ) => component_by_expansion.get(expansion.0 as usize).copied(),
                _ => None,
            };
            if matches!(edge.to, GraphNode::Expansion(_))
                && matches!(
                    edge.kind,
                    DependencyKind::ExpansionUse | DependencyKind::GeneratedBy
                )
                && target_component.is_none()
            {
                return Err(RetentionError::InvalidGraph);
            }

            let edge_id = edges.len();
            edges.push(IndexedCompilerEdge {
                from: edge.from,
                to: edge.to,
                site_unconditional,
                target_component,
            });
            edges_by_from.entry(edge.from).or_default().push(edge_id);
            if !site_unconditional {
                if edge_source_sites.is_empty() {
                    return Err(RetentionError::InvalidGraph);
                }
                for site in edge_source_sites {
                    source_sites[site].edges.push(edge_id);
                }
            }
            if let Some(component) = target_component {
                components[component].target_edges.push(edge_id);
            }
        }

        for sites in &mut sites_by_source {
            sites.sort_unstable();
            sites.dedup();
        }
        for edges in edges_by_from.values_mut() {
            edges.sort_unstable();
            edges.dedup();
        }
        for component in &mut components {
            component.target_edges.sort_unstable();
            component.target_edges.dedup();
        }

        let mut components_by_source = vec![Vec::new(); source.units.len()];
        for (component, facts) in components.iter().enumerate() {
            for source_unit in &facts.source_units {
                components_by_source[source_unit.0 as usize].push(component);
            }
        }

        Ok(Self {
            edges,
            edges_by_from,
            source_sites,
            sites_by_source,
            components,
            components_by_source,
        })
    }
}

/// Stateful monotone compiler reachability. Every source unit, expansion
/// component, reachable node, and compiler edge is consumed only when one of
/// its gates changes from false to true.
pub(super) struct CompilerReachabilityClosure<'index> {
    index: &'index CompilerReachabilityIndex,
    initialized: bool,
    retained_sources: Vec<bool>,
    reachable_nodes: BTreeSet<GraphNode>,
    site_retained_owners: Vec<usize>,
    site_states: Vec<u8>,
    dirty_sites: BTreeSet<usize>,
    component_missing_sources: Vec<usize>,
    component_missing_parents: Vec<usize>,
    component_survives: Vec<bool>,
    edge_site_open: Vec<bool>,
    edge_partial_sites: Vec<usize>,
    edge_fired: Vec<bool>,
    edge_pending: Vec<bool>,
    pending_nodes: VecDeque<GraphNode>,
    pending_components: VecDeque<usize>,
    pending_edges: VecDeque<usize>,
    #[cfg(test)]
    pub(super) node_visits: usize,
    #[cfg(test)]
    pub(super) edge_visits: usize,
    #[cfg(test)]
    pub(super) site_owner_visits: usize,
    #[cfg(test)]
    pub(super) component_fact_visits: usize,
}

impl<'index> CompilerReachabilityClosure<'index> {
    pub(super) fn new(index: &'index CompilerReachabilityIndex) -> Self {
        let mut closure = Self {
            index,
            initialized: false,
            retained_sources: vec![false; index.sites_by_source.len()],
            reachable_nodes: BTreeSet::new(),
            site_retained_owners: vec![0; index.source_sites.len()],
            site_states: vec![0; index.source_sites.len()],
            dirty_sites: BTreeSet::new(),
            component_missing_sources: index
                .components
                .iter()
                .map(|component| component.source_units.len())
                .collect(),
            component_missing_parents: index
                .components
                .iter()
                .map(|component| component.parents.len())
                .collect(),
            component_survives: vec![false; index.components.len()],
            edge_site_open: index
                .edges
                .iter()
                .map(|edge| edge.site_unconditional)
                .collect(),
            edge_partial_sites: vec![0; index.edges.len()],
            edge_fired: vec![false; index.edges.len()],
            edge_pending: vec![false; index.edges.len()],
            pending_nodes: VecDeque::new(),
            pending_components: VecDeque::new(),
            pending_edges: VecDeque::new(),
            #[cfg(test)]
            node_visits: 0,
            #[cfg(test)]
            edge_visits: 0,
            #[cfg(test)]
            site_owner_visits: 0,
            #[cfg(test)]
            component_fact_visits: 0,
        };
        for component in 0..index.components.len() {
            closure.queue_component_if_ready(component);
        }
        closure
    }

    pub(super) fn seed(
        &mut self,
        reachable: &BTreeSet<GraphNode>,
        retained_sources: &BTreeSet<SourceUnitId>,
    ) -> Result<(), RetentionError> {
        if self.initialized {
            return Err(RetentionError::InvalidConstraint);
        }
        self.initialized = true;
        self.add_sources(retained_sources.iter().copied())?;
        self.add_reachable(reachable.iter().copied());
        Ok(())
    }

    pub(super) fn add_reachable(&mut self, nodes: impl IntoIterator<Item = GraphNode>) {
        for node in nodes {
            if self.reachable_nodes.insert(node) {
                self.pending_nodes.push_back(node);
            }
        }
    }

    pub(super) fn add_sources(
        &mut self,
        units: impl IntoIterator<Item = SourceUnitId>,
    ) -> Result<(), RetentionError> {
        let mut affected_components = BTreeSet::new();
        for unit in units {
            let Some(retained) = self.retained_sources.get_mut(unit.0 as usize) else {
                return Err(RetentionError::InvalidGraph);
            };
            if *retained {
                continue;
            }
            *retained = true;
            for &site in &self.index.sites_by_source[unit.0 as usize] {
                #[cfg(test)]
                {
                    self.site_owner_visits += 1;
                }
                self.site_retained_owners[site] += 1;
                self.dirty_sites.insert(site);
            }
            for &component in &self.index.components_by_source[unit.0 as usize] {
                #[cfg(test)]
                {
                    self.component_fact_visits += 1;
                }
                let missing = &mut self.component_missing_sources[component];
                if *missing == 0 {
                    return Err(RetentionError::InvalidGraph);
                }
                *missing -= 1;
                affected_components.insert(component);
            }
        }

        for component in affected_components {
            self.queue_component_if_ready(component);
        }
        Ok(())
    }

    pub(super) fn close(
        &mut self,
        reachable: &mut BTreeSet<GraphNode>,
        newly_reachable: &mut Vec<GraphNode>,
    ) -> Result<(), RetentionError> {
        for site in std::mem::take(&mut self.dirty_sites) {
            let retained = self.site_retained_owners[site];
            let owners = self.index.source_sites[site].owners.len();
            if retained > owners {
                return Err(RetentionError::InvalidGraph);
            }
            let state = if retained == 0 {
                0
            } else if retained == owners {
                2
            } else {
                1
            };
            let previous = self.site_states[site];
            if state == previous {
                continue;
            }
            self.site_states[site] = state;
            for &edge in &self.index.source_sites[site].edges {
                if previous == 1 {
                    let partial = &mut self.edge_partial_sites[edge];
                    if *partial == 0 {
                        return Err(RetentionError::InvalidGraph);
                    }
                    *partial -= 1;
                }
                if state == 1 {
                    self.edge_partial_sites[edge] += 1;
                } else if state == 2 {
                    self.edge_site_open[edge] = true;
                }
                self.queue_edge(edge);
            }
        }
        while !self.pending_components.is_empty()
            || !self.pending_nodes.is_empty()
            || !self.pending_edges.is_empty()
        {
            while let Some(component) = self.pending_components.pop_front() {
                if self.component_survives[component]
                    || self.component_missing_sources[component] != 0
                    || self.component_missing_parents[component] != 0
                {
                    continue;
                }
                self.component_survives[component] = true;
                for &edge in &self.index.components[component].target_edges {
                    self.queue_edge(edge);
                }
                for &child in &self.index.components[component].children {
                    #[cfg(test)]
                    {
                        self.component_fact_visits += 1;
                    }
                    let missing = &mut self.component_missing_parents[child];
                    if *missing != 0 {
                        *missing -= 1;
                    }
                    self.queue_component_if_ready(child);
                }
            }
            while let Some(node) = self.pending_nodes.pop_front() {
                #[cfg(test)]
                {
                    self.node_visits += 1;
                }
                if let Some(edges) = self.index.edges_by_from.get(&node) {
                    for &edge in edges {
                        self.queue_edge(edge);
                    }
                }
            }
            while let Some(edge) = self.pending_edges.pop_front() {
                self.edge_pending[edge] = false;
                if self.edge_fired[edge] {
                    continue;
                }
                #[cfg(test)]
                {
                    self.edge_visits += 1;
                }
                let facts = &self.index.edges[edge];
                if !self.reachable_nodes.contains(&facts.from)
                    || facts
                        .target_component
                        .is_some_and(|component| !self.component_survives[component])
                {
                    continue;
                }
                if !self.edge_site_open[edge] {
                    if self.edge_partial_sites[edge] != 0 {
                        return Err(RetentionError::InvalidGraph);
                    }
                    continue;
                }
                self.edge_fired[edge] = true;
                if reachable.insert(facts.to) {
                    newly_reachable.push(facts.to);
                }
                if self.reachable_nodes.insert(facts.to) {
                    self.pending_nodes.push_back(facts.to);
                }
            }
        }
        Ok(())
    }

    fn queue_component_if_ready(&mut self, component: usize) {
        if !self.component_survives[component]
            && self.component_missing_sources[component] == 0
            && self.component_missing_parents[component] == 0
        {
            self.pending_components.push_back(component);
        }
    }

    fn queue_edge(&mut self, edge: usize) {
        if !self.edge_fired[edge] && !self.edge_pending[edge] {
            self.edge_pending[edge] = true;
            self.pending_edges.push_back(edge);
        }
    }
}

fn expansion_components(
    source: &SourceInventory,
    graph: &DependencyGraph,
) -> Result<(Vec<usize>, Vec<ExpansionComponent>), RetentionError> {
    let count = graph.expansions.len();
    let mut parents = vec![Vec::new(); count];
    let mut children = vec![Vec::new(); count];
    for (index, expansion) in graph.expansions.iter().enumerate() {
        if expansion.id.0 as usize != index {
            return Err(RetentionError::InvalidGraph);
        }
        for parent in [
            expansion.discovered_in,
            expansion.semantic_parent,
            expansion.source_call_parent,
        ]
        .into_iter()
        .flatten()
        {
            let parent = parent.0 as usize;
            if parent >= count || parent == index {
                return Err(RetentionError::InvalidGraph);
            }
            parents[index].push(parent);
            children[parent].push(index);
        }
        parents[index].sort_unstable();
        parents[index].dedup();
    }
    for children in &mut children {
        children.sort_unstable();
        children.dedup();
    }

    let mut visited = vec![false; count];
    let mut finish = Vec::with_capacity(count);
    for start in 0..count {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        let mut stack = vec![(start, 0_usize)];
        while let Some((node, next)) = stack.last_mut() {
            if *next < parents[*node].len() {
                let parent = parents[*node][*next];
                *next += 1;
                if !visited[parent] {
                    visited[parent] = true;
                    stack.push((parent, 0));
                }
            } else {
                finish.push(*node);
                stack.pop();
            }
        }
    }

    let mut component_by_expansion = vec![usize::MAX; count];
    let mut members = Vec::<Vec<usize>>::new();
    for start in finish.into_iter().rev() {
        if component_by_expansion[start] != usize::MAX {
            continue;
        }
        let component = members.len();
        let mut component_members = Vec::new();
        let mut stack = vec![start];
        component_by_expansion[start] = component;
        while let Some(node) = stack.pop() {
            component_members.push(node);
            for &child in &children[node] {
                if component_by_expansion[child] == usize::MAX {
                    component_by_expansion[child] = component;
                    stack.push(child);
                }
            }
        }
        component_members.sort_unstable();
        members.push(component_members);
    }

    let mut components = members
        .iter()
        .map(|_| ExpansionComponent {
            source_units: Vec::new(),
            parents: Vec::new(),
            children: Vec::new(),
            target_edges: Vec::new(),
        })
        .collect::<Vec<_>>();
    for (component, component_members) in members.iter().enumerate() {
        for &expansion in component_members {
            let facts = &graph.expansions[expansion];
            if let Some(unit) = facts.written_invocation {
                let written = source
                    .units
                    .get(unit.0 as usize)
                    .filter(|written| {
                        written.id == unit
                            && written.kind == WrittenUnitKind::MacroInvocation
                            && written.cfg_state == CfgState::Active
                    })
                    .ok_or(RetentionError::InvalidGraph)?;
                components[component].source_units.push(written.id);
            }
            for &parent in &parents[expansion] {
                let parent_component = component_by_expansion[parent];
                if parent_component != component {
                    components[component].parents.push(parent_component);
                }
            }
        }
        components[component].source_units.sort_unstable();
        components[component].source_units.dedup();
        components[component].parents.sort_unstable();
        components[component].parents.dedup();
    }
    for component in 0..components.len() {
        for parent in components[component].parents.clone() {
            components[parent].children.push(component);
        }
    }
    for component in &mut components {
        component.children.sort_unstable();
        component.children.dedup();
    }

    Ok((component_by_expansion, components))
}
