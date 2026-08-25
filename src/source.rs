use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use rustc_ast as ast;
use rustc_ast::HasAttrs;
use rustc_ast::tokenstream::WithTokens;
use rustc_ast::visit::{self, AssocCtxt, Visitor};
#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::unord::UnordMap;
use rustc_expand::config::{StripUnconfigured, features, pre_configure_attrs};
use rustc_feature::Features;
use rustc_interface::interface::Compiler;
use rustc_lexer::{FrontmatterAllowed, TokenKind, strip_shebang, tokenize};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{MacroImplementationKind, MacroInvocationOrigin, TyCtxt};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::{ExpnId, ExpnKind, MacroKind};
use rustc_span::{SourceFile, Span, Symbol, sym};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ByteRange {
    pub start: u32,
    pub end: u32,
}

impl ByteRange {
    pub fn contains(self, other: Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    pub fn len(self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SourceUnitId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AtomicGroupId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CfgState {
    Active,
    Inactive,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum WrittenUnitKind {
    CrateRoot,
    InlineModule,
    Item,
    TraitMember,
    ImplMember,
    UseItem,
    UseLeaf,
    MacroDefinition,
    MacroInvocation,
    NestedItem,
    MacroRule,
}

impl WrittenUnitKind {
    pub(crate) fn rank(self) -> u8 {
        match self {
            Self::CrateRoot => 0,
            Self::InlineModule => 1,
            Self::Item => 2,
            Self::TraitMember => 3,
            Self::ImplMember => 4,
            Self::UseItem => 5,
            Self::UseLeaf => 6,
            Self::MacroDefinition => 7,
            Self::MacroInvocation => 8,
            Self::NestedItem => 9,
            Self::MacroRule => 10,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenUnit {
    pub id: SourceUnitId,
    pub kind: WrittenUnitKind,
    pub full_range: ByteRange,
    pub parent: Option<SourceUnitId>,
    pub cfg_state: CfgState,
    pub atomic_group: AtomicGroupId,
    pub same_role_ordinal: u32,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PieceKind {
    Token,
    Trivia,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct OwnedPiece {
    pub range: ByteRange,
    pub owner: SourceUnitId,
    pub kind: PieceKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceInventory {
    pub original: Arc<str>,
    pub(crate) normalized: Arc<str>,
    pub(crate) offsets: OriginalOffsetMap,
    pub units: Vec<WrittenUnit>,
    pub pieces: Vec<OwnedPiece>,
    pub(crate) macro_rules: Vec<MacroRuleSourceFacts>,
    pub(crate) ownerless_attribute_invocations: Vec<SourceUnitId>,
}

impl SourceInventory {
    pub(crate) fn ownerless_attribute_target(
        &self,
        invocation: SourceUnitId,
    ) -> Option<SourceUnitId> {
        self.ownerless_attribute_invocations
            .binary_search(&invocation)
            .ok()?;
        self.units.get(invocation.0 as usize)?.parent
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct AttributeSource {
    pub invocation: Option<SourceUnitId>,
    pub target: SourceUnitId,
}

pub(crate) fn resolve_attribute_source(
    inventory: &SourceInventory,
    invocation_range: ByteRange,
    node_range: ByteRange,
    target_range: ByteRange,
) -> Result<AttributeSource, SourceError> {
    if invocation_range.start >= invocation_range.end
        || !node_range.contains(invocation_range)
        || !node_range.contains(target_range)
    {
        return Err(SourceError::IncompleteAttributeObservation);
    }
    let mut targets = inventory
        .units
        .iter()
        .filter(|unit| {
            unit.cfg_state == CfgState::Active
                && unit.full_range.contains(node_range)
                && unit.full_range.contains(target_range)
                && unit.full_range.contains(invocation_range)
        })
        .collect::<Vec<_>>();
    let smallest = targets
        .iter()
        .map(|unit| unit.full_range.len())
        .min()
        .ok_or(SourceError::IncompleteAttributeObservation)?;
    targets.retain(|unit| unit.full_range.len() == smallest);
    let [target] = targets.as_slice() else {
        return Err(SourceError::IncompleteAttributeObservation);
    };

    let invocations = inventory
        .units
        .iter()
        .filter(|unit| {
            unit.kind == WrittenUnitKind::MacroInvocation
                && unit.cfg_state == CfgState::Active
                && unit.parent == Some(target.id)
                && unit.atomic_group == target.atomic_group
                && unit.full_range.end <= target_range.start
                && (unit.full_range == invocation_range
                    || unit.full_range.contains(invocation_range))
        })
        .map(|unit| unit.id)
        .collect::<Vec<_>>();
    let invocation = match invocations.as_slice() {
        [] => None,
        [invocation] => Some(*invocation),
        _ => return Err(SourceError::IncompleteAttributeObservation),
    };
    Ok(AttributeSource {
        invocation,
        target: target.id,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroRuleSourceFacts {
    Whole {
        definition: SourceUnitId,
    },
    Refined {
        definition: SourceUnitId,
        rules: Vec<SourceUnitId>,
        /// One rule ID per observed expansion. Repeated IDs preserve the
        /// coverage needed when several expansions select the same rule.
        observed_selections: Vec<SourceUnitId>,
    },
}

impl MacroRuleSourceFacts {
    pub(crate) fn definition(&self) -> SourceUnitId {
        match self {
            Self::Whole { definition } | Self::Refined { definition, .. } => *definition,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ObservedMacroRules {
    pub definition_range: ByteRange,
    pub rule_ranges: Vec<ByteRange>,
    pub selected_rule_indices: Vec<usize>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ObservedAttributeMacro {
    invocation_range: ByteRange,
    node_range: ByteRange,
    target_range: ByteRange,
    target_survives: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ObservedProceduralMacro {
    Invocation {
        invocation_range: ByteRange,
        node_range: ByteRange,
    },
    Target {
        invocation_range: ByteRange,
        node_range: ByteRange,
        target_range: ByteRange,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NormalizationRecord {
    normalized_at: u32,
    diff: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OriginalOffsetMap {
    original_len: u32,
    normalized_len: u32,
    records: Vec<NormalizationRecord>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SourceError {
    SourceTooLarge,
    NormalizationMismatch,
    InvalidSpan,
    InvalidInventory,
    IncompleteAttributeObservation,
    IncompleteMacroRuleObservation,
    IncompleteProceduralMacroObservation,
}

impl OriginalOffsetMap {
    pub(crate) fn from_source(source: &str) -> Result<(String, Self), SourceError> {
        let original_len = u32::try_from(source.len()).map_err(|_| SourceError::SourceTooLarge)?;
        if original_len == u32::MAX {
            return Err(SourceError::SourceTooLarge);
        }

        let bytes = source.as_bytes();
        let mut normalized = Vec::with_capacity(bytes.len());
        let mut records = Vec::new();
        let mut input = 0_usize;
        let mut diff = 0_u32;

        if bytes.starts_with(&[0xef, 0xbb, 0xbf]) {
            input = 3;
            diff = 3;
            records.push(NormalizationRecord {
                normalized_at: 0,
                diff,
            });
        }

        while input < bytes.len() {
            if bytes[input..].starts_with(b"\r\n") {
                normalized.push(b'\n');
                input += 2;
                diff += 1;
                records.push(NormalizationRecord {
                    normalized_at: u32::try_from(normalized.len())
                        .map_err(|_| SourceError::SourceTooLarge)?,
                    diff,
                });
            } else {
                normalized.push(bytes[input]);
                input += 1;
            }
        }

        let normalized =
            String::from_utf8(normalized).map_err(|_| SourceError::NormalizationMismatch)?;
        let normalized_len =
            u32::try_from(normalized.len()).map_err(|_| SourceError::SourceTooLarge)?;
        let map = Self {
            original_len,
            normalized_len,
            records,
        };
        map.validate()?;
        Ok((normalized, map))
    }

    fn validate_source_file(&self, source_file: &SourceFile) -> Result<(), SourceError> {
        if source_file.unnormalized_source_len != self.original_len
            || source_file.normalized_source_len.0 != self.normalized_len
            || source_file.normalized_pos.len() != self.records.len()
            || source_file
                .normalized_pos
                .iter()
                .zip(&self.records)
                .any(|(actual, expected)| {
                    actual.pos.0 != expected.normalized_at || actual.diff != expected.diff
                })
        {
            return Err(SourceError::NormalizationMismatch);
        }
        Ok(())
    }

    fn validate(&self) -> Result<(), SourceError> {
        let mut previous_normalized = 0;
        let mut previous_diff = 0;
        for (index, record) in self.records.iter().enumerate() {
            if record.normalized_at > self.normalized_len
                || record.diff <= previous_diff
                || (index > 0 && record.normalized_at <= previous_normalized)
                || record.normalized_at.checked_add(record.diff).is_none()
                || record.normalized_at + record.diff > self.original_len
            {
                return Err(SourceError::NormalizationMismatch);
            }
            if self.normalized_from_original(self.left(record.normalized_at)?)?
                != record.normalized_at
                || self.normalized_from_original(self.right(record.normalized_at)?)?
                    != record.normalized_at
            {
                return Err(SourceError::NormalizationMismatch);
            }
            previous_normalized = record.normalized_at;
            previous_diff = record.diff;
        }

        if self.right(self.normalized_len)? != self.original_len
            || self.normalized_from_original(self.original_len)? != self.normalized_len
        {
            return Err(SourceError::NormalizationMismatch);
        }
        Ok(())
    }

    fn left(&self, normalized: u32) -> Result<u32, SourceError> {
        self.map_endpoint(normalized, false)
    }

    fn right(&self, normalized: u32) -> Result<u32, SourceError> {
        self.map_endpoint(normalized, true)
    }

    fn map_endpoint(&self, normalized: u32, right_bias: bool) -> Result<u32, SourceError> {
        if normalized > self.normalized_len {
            return Err(SourceError::InvalidSpan);
        }
        let diff = match self
            .records
            .binary_search_by_key(&normalized, |record| record.normalized_at)
        {
            Ok(index) if right_bias => self.records[index].diff,
            Ok(0) => 0,
            Ok(index) => self.records[index - 1].diff,
            Err(0) => 0,
            Err(index) => self.records[index - 1].diff,
        };
        normalized
            .checked_add(diff)
            .filter(|&position| position <= self.original_len)
            .ok_or(SourceError::InvalidSpan)
    }

    fn normalized_from_original(&self, original: u32) -> Result<u32, SourceError> {
        if original > self.original_len {
            return Err(SourceError::InvalidSpan);
        }
        let mut previous_diff = 0;
        for record in &self.records {
            let removed_start = record.normalized_at + previous_diff;
            let removed_end = record.normalized_at + record.diff;
            if original < removed_start {
                return original
                    .checked_sub(previous_diff)
                    .ok_or(SourceError::InvalidSpan);
            }
            if original <= removed_end {
                return Ok(record.normalized_at);
            }
            previous_diff = record.diff;
        }
        original
            .checked_sub(previous_diff)
            .ok_or(SourceError::InvalidSpan)
    }

    pub(crate) fn original_range(&self, normalized: ByteRange) -> Result<ByteRange, SourceError> {
        if normalized.start > normalized.end || normalized.end > self.normalized_len {
            return Err(SourceError::InvalidSpan);
        }
        if normalized.start == normalized.end {
            let point = self.right(normalized.start)?;
            return Ok(ByteRange {
                start: point,
                end: point,
            });
        }
        let range = ByteRange {
            start: self.right(normalized.start)?,
            end: self.left(normalized.end)?,
        };
        if range.start > range.end {
            return Err(SourceError::InvalidSpan);
        }
        Ok(range)
    }
}

#[derive(Clone, Debug)]
struct PendingUnit {
    temporary_id: u32,
    kind: WrittenUnitKind,
    full_range: ByteRange,
    parent: Option<u32>,
    cfg_state: CfgState,
    atomic_representative: u32,
    syntax_ordinal: u32,
}

fn pending_units(units: &[WrittenUnit]) -> (Vec<PendingUnit>, BTreeMap<AtomicGroupId, u32>) {
    let representatives = units.iter().fold(
        BTreeMap::<AtomicGroupId, u32>::new(),
        |mut representatives, unit| {
            representatives
                .entry(unit.atomic_group)
                .or_insert(unit.id.0);
            representatives
        },
    );
    let pending = units
        .iter()
        .map(|unit| PendingUnit {
            temporary_id: unit.id.0,
            kind: unit.kind,
            full_range: unit.full_range,
            parent: unit.parent.map(|parent| parent.0),
            cfg_state: unit.cfg_state,
            atomic_representative: representatives[&unit.atomic_group],
            syntax_ordinal: unit.id.0,
        })
        .collect();
    (pending, representatives)
}

pub(crate) fn collect_source(
    compiler: &Compiler,
    krate: &ast::Crate,
    original: Arc<str>,
) -> Result<SourceInventory, SourceError> {
    let (normalized, offsets) = OriginalOffsetMap::from_source(&original)?;
    let source_file = main_source_file(compiler, krate)?;
    offsets.validate_source_file(&source_file)?;
    if source_file.src.as_deref().map(String::as_str) != Some(normalized.as_str()) {
        return Err(SourceError::NormalizationMismatch);
    }

    let configured_attrs = pre_configure_attrs(&compiler.sess, &krate.attrs);
    let crate_name = compiler
        .sess
        .opts
        .crate_name
        .as_deref()
        .ok_or(SourceError::InvalidInventory)?;
    let features = features(
        &compiler.sess,
        &configured_attrs,
        Symbol::intern(crate_name),
    );
    let root_active = StripUnconfigured {
        sess: &compiler.sess,
        features: Some(&features),
        config_tokens: false,
        lint_node_id: ast::CRATE_NODE_ID,
    }
    .configure(WithTokens::new(krate.clone()))
    .is_some();
    let mut collector = UnitCollector::new(
        compiler,
        source_file,
        &offsets,
        features,
        root_active,
        original.len(),
    )?;
    collector.record_configured_attribute_macros(&krate.attrs, &configured_attrs, root_active);
    collector.visit_crate(krate);
    let units = collector.finish()?;
    let pieces = own_lexical_pieces(&original, &units)?;
    validate_inventory(&original, &units, &pieces)?;

    Ok(SourceInventory {
        original,
        normalized: Arc::from(normalized),
        offsets,
        units,
        pieces,
        macro_rules: Vec::new(),
        ownerless_attribute_invocations: Vec::new(),
    })
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn refine_attribute_macros_from_compiler(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    expanded: &ast::Crate,
    inventory: &mut SourceInventory,
) -> Result<(), SourceError> {
    #[derive(Default)]
    struct SurvivingTargetCollector {
        spans: Vec<Span>,
    }

    impl SurvivingTargetCollector {
        fn record(&mut self, span: Span) {
            if !span.from_expansion() {
                self.spans.push(span);
            }
        }
    }

    impl<'ast> Visitor<'ast> for SurvivingTargetCollector {
        fn visit_item(&mut self, item: &'ast ast::Item) {
            self.record(item.span);
            visit::walk_item(self, item);
        }

        fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: AssocCtxt) {
            self.record(item.span);
            visit::walk_assoc_item(self, item, context);
        }

        fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
            self.record(item.span);
            visit::walk_item(self, item);
        }
    }

    let mut surviving = SurvivingTargetCollector::default();
    surviving.visit_crate(expanded);
    let surviving = surviving
        .spans
        .into_iter()
        .map(|span| original_span_range(compiler, &inventory.offsets, span))
        .collect::<Result<BTreeSet<_>, _>>()?;

    let origins = tcx
        .resolutions(())
        .macro_invocation_origins
        .items()
        .map(|(&expansion, origin)| {
            (
                expansion.expn_hash().local_hash().as_u64(),
                expansion,
                origin,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    let mut observations = Vec::new();
    for (_, expansion, origin) in origins {
        let observation = (|| -> Result<Option<ObservedAttributeMacro>, SourceError> {
            let ExpnKind::Macro(MacroKind::Attr, _) = expansion.expn_data().kind else {
                return Ok(None);
            };
            if origin.discovered_in_expansion != ExpnId::root() {
                return Ok(None);
            }
            let target_span = origin
                .target_span
                .ok_or(SourceError::IncompleteAttributeObservation)?;
            let invocation_range = original_span_range(
                compiler,
                &inventory.offsets,
                expansion.expn_data().call_site,
            )?;
            let node_range =
                original_span_range(compiler, &inventory.offsets, origin.invocation_node_span)?;
            let target_range = original_span_range(compiler, &inventory.offsets, target_span)?;
            Ok(Some(ObservedAttributeMacro {
                invocation_range,
                node_range,
                target_range,
                target_survives: surviving.contains(&target_range),
            }))
        })()?;
        if let Some(observation) = observation {
            observations.push(observation);
        }
    }
    observations.sort();
    if observations.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(SourceError::IncompleteAttributeObservation);
    }
    refine_attribute_macros(inventory, observations)
}

#[cfg(rust_item_dependencies_patched)]
fn refine_attribute_macros(
    inventory: &mut SourceInventory,
    observations: Vec<ObservedAttributeMacro>,
) -> Result<(), SourceError> {
    if !inventory.macro_rules.is_empty()
        || !inventory.ownerless_attribute_invocations.is_empty()
        || inventory
            .units
            .iter()
            .any(|unit| unit.kind == WrittenUnitKind::MacroRule)
    {
        return Err(SourceError::InvalidInventory);
    }
    validate_inventory(&inventory.original, &inventory.units, &inventory.pieces)?;

    let (mut pending, representatives) = pending_units(&inventory.units);
    let mut next_temporary =
        u32::try_from(pending.len()).map_err(|_| SourceError::SourceTooLarge)?;
    let mut ownerless_invocations = BTreeSet::new();
    let mut replaced_targets = BTreeMap::<u32, BTreeSet<u32>>::new();

    for observation in observations {
        let source = resolve_attribute_source(
            inventory,
            observation.invocation_range,
            observation.node_range,
            observation.target_range,
        )?;
        let target = &inventory.units[source.target.0 as usize];
        let invocation = match source.invocation {
            None => {
                let temporary_id = next_temporary;
                next_temporary = next_temporary
                    .checked_add(1)
                    .ok_or(SourceError::SourceTooLarge)?;
                pending.push(PendingUnit {
                    temporary_id,
                    kind: WrittenUnitKind::MacroInvocation,
                    full_range: observation.invocation_range,
                    parent: Some(target.id.0),
                    cfg_state: CfgState::Active,
                    atomic_representative: representatives[&target.atomic_group],
                    syntax_ordinal: temporary_id,
                });
                temporary_id
            }
            Some(invocation) => invocation.0,
        };
        if !observation.target_survives {
            match target.kind {
                WrittenUnitKind::Item
                | WrittenUnitKind::NestedItem
                | WrittenUnitKind::InlineModule => {
                    replaced_targets
                        .entry(target.id.0)
                        .or_default()
                        .insert(invocation);
                }
                WrittenUnitKind::MacroInvocation => {}
                _ => return Err(SourceError::IncompleteAttributeObservation),
            }
            ownerless_invocations.insert(invocation);
        }
    }

    let parents = pending
        .iter()
        .map(|unit| (unit.temporary_id, unit.parent))
        .collect::<BTreeMap<_, _>>();
    let mut removed = BTreeSet::new();
    for (&target, invocations) in &replaced_targets {
        for unit in &pending {
            if unit.temporary_id == target || invocations.contains(&unit.temporary_id) {
                continue;
            }
            let mut parent = unit.parent;
            while let Some(candidate) = parent {
                if candidate == target {
                    removed.insert(unit.temporary_id);
                    break;
                }
                parent = parents
                    .get(&candidate)
                    .copied()
                    .ok_or(SourceError::IncompleteAttributeObservation)?;
            }
        }
    }
    pending.retain(|unit| !removed.contains(&unit.temporary_id));

    let (units, id_map) = finish_pending_units(pending)?;
    let mut ownerless_attribute_invocations = ownerless_invocations
        .into_iter()
        .map(|invocation| id_map[&invocation])
        .collect::<Vec<_>>();
    ownerless_attribute_invocations.sort();
    let pieces = own_lexical_pieces(&inventory.original, &units)?;
    validate_inventory(&inventory.original, &units, &pieces)?;
    validate_ownerless_attribute_invocations(&units, &ownerless_attribute_invocations)?;
    inventory.units = units;
    inventory.pieces = pieces;
    inventory.ownerless_attribute_invocations = ownerless_attribute_invocations;
    Ok(())
}

pub(crate) fn refine_macro_rules(
    inventory: &mut SourceInventory,
    observations: Vec<ObservedMacroRules>,
) -> Result<(), SourceError> {
    refine_macro_rules_outside_opaque_anchors(inventory, observations, &BTreeSet::new())
}

fn refine_macro_rules_outside_opaque_anchors(
    inventory: &mut SourceInventory,
    mut observations: Vec<ObservedMacroRules>,
    opaque_anchors: &BTreeSet<ByteRange>,
) -> Result<(), SourceError> {
    if !inventory.macro_rules.is_empty()
        || inventory
            .units
            .iter()
            .any(|unit| unit.kind == WrittenUnitKind::MacroRule)
    {
        return Err(SourceError::InvalidInventory);
    }
    validate_inventory(&inventory.original, &inventory.units, &inventory.pieces)?;
    validate_ownerless_attribute_invocations(
        &inventory.units,
        &inventory.ownerless_attribute_invocations,
    )?;
    observations.retain(|observation| {
        !opaque_anchors
            .iter()
            .any(|anchor| anchor.contains(observation.definition_range))
    });
    observations.sort_by_key(|observation| observation.definition_range);
    if observations
        .windows(2)
        .any(|pair| pair[0].definition_range == pair[1].definition_range)
    {
        return Err(SourceError::InvalidInventory);
    }

    let (mut pending, _) = pending_units(&inventory.units);
    let mut next_temporary =
        u32::try_from(pending.len()).map_err(|_| SourceError::SourceTooLarge)?;
    let mut refined_facts = Vec::new();
    let mut whole_definitions = Vec::new();
    let mut classified_definitions = BTreeSet::new();

    for observation in observations {
        if !valid_source_range(&inventory.original, observation.definition_range)
            || observation.rule_ranges.is_empty()
            || observation.rule_ranges.iter().any(|range| {
                !valid_source_range(&inventory.original, *range)
                    || range.start == range.end
                    || !observation.definition_range.contains(*range)
            })
            || observation
                .rule_ranges
                .windows(2)
                .any(|pair| pair[0].end > pair[1].start)
        {
            return Err(SourceError::InvalidInventory);
        }
        let mut selected = observation.selected_rule_indices;
        if selected
            .iter()
            .any(|index| *index >= observation.rule_ranges.len())
        {
            return Err(SourceError::InvalidInventory);
        }
        selected.sort_unstable();

        let candidates = inventory
            .units
            .iter()
            .filter(|unit| {
                unit.kind == WrittenUnitKind::MacroDefinition
                    && unit.cfg_state == CfgState::Active
                    && unit.full_range.contains(observation.definition_range)
            })
            .collect::<Vec<_>>();
        let [definition] = candidates.as_slice() else {
            return Err(SourceError::InvalidInventory);
        };
        if !classified_definitions.insert(definition.id) {
            return Err(SourceError::InvalidInventory);
        }

        let mut rules = Vec::with_capacity(observation.rule_ranges.len());
        for range in observation.rule_ranges {
            let temporary_id = next_temporary;
            next_temporary = next_temporary
                .checked_add(1)
                .ok_or(SourceError::SourceTooLarge)?;
            pending.push(PendingUnit {
                temporary_id,
                kind: WrittenUnitKind::MacroRule,
                full_range: range,
                parent: Some(definition.id.0),
                cfg_state: CfgState::Active,
                atomic_representative: temporary_id,
                syntax_ordinal: temporary_id,
            });
            rules.push(temporary_id);
        }
        let observed = selected
            .into_iter()
            .map(|index| rules[index])
            .collect::<Vec<_>>();
        refined_facts.push((definition.id.0, rules, observed));
    }
    for definition in inventory.units.iter().filter(|unit| {
        unit.kind == WrittenUnitKind::MacroDefinition
            && unit.cfg_state == CfgState::Active
            && opaque_anchors
                .iter()
                .any(|anchor| anchor.contains(unit.full_range))
    }) {
        if !classified_definitions.insert(definition.id) {
            return Err(SourceError::InvalidInventory);
        }
        whole_definitions.push(definition.id.0);
    }
    let expected_definitions = inventory
        .units
        .iter()
        .filter(|unit| {
            unit.kind == WrittenUnitKind::MacroDefinition && unit.cfg_state == CfgState::Active
        })
        .map(|unit| unit.id)
        .collect::<BTreeSet<_>>();
    if classified_definitions != expected_definitions {
        return Err(SourceError::IncompleteMacroRuleObservation);
    }
    let (units, id_map) = finish_pending_units(pending)?;
    let mut macro_rules = Vec::with_capacity(whole_definitions.len() + refined_facts.len());
    for definition in whole_definitions {
        macro_rules.push(MacroRuleSourceFacts::Whole {
            definition: id_map[&definition],
        });
    }
    for (definition, rules, observed_selections) in refined_facts {
        macro_rules.push(MacroRuleSourceFacts::Refined {
            definition: id_map[&definition],
            rules: rules.into_iter().map(|rule| id_map[&rule]).collect(),
            observed_selections: observed_selections
                .into_iter()
                .map(|rule| id_map[&rule])
                .collect(),
        });
    }
    macro_rules.sort_by_key(MacroRuleSourceFacts::definition);
    let mut ownerless_attribute_invocations = inventory
        .ownerless_attribute_invocations
        .iter()
        .map(|invocation| id_map[&invocation.0])
        .collect::<Vec<_>>();
    ownerless_attribute_invocations.sort();
    let pieces = own_lexical_pieces(&inventory.original, &units)?;
    validate_inventory(&inventory.original, &units, &pieces)?;
    validate_macro_rule_facts(&units, &macro_rules)?;
    validate_ownerless_attribute_invocations(&units, &ownerless_attribute_invocations)?;
    inventory.units = units;
    inventory.pieces = pieces;
    inventory.macro_rules = macro_rules;
    inventory.ownerless_attribute_invocations = ownerless_attribute_invocations;
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn refine_macro_rules_from_compiler(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &mut SourceInventory,
    mut omit_one_selection: bool,
) -> Result<(), SourceError> {
    let procedural = collect_procedural_macro_observations(compiler, tcx, inventory)?;
    let opaque_anchors = resolve_procedural_macro_anchors(inventory, procedural)?;
    let resolutions = tcx.resolutions(());
    let definitions = &resolutions.macro_rules_definitions;
    let ordered_definitions = definitions
        .items()
        .map(|(&definition, rules)| (definition.local_def_index.as_u32(), definition, rules))
        .into_sorted_stable_ord_by_key(|record| &record.0);
    let mut selected = ordered_definitions
        .iter()
        .map(|(index, _, _)| (*index, Vec::new()))
        .collect::<BTreeMap<_, _>>();

    let origins = resolutions
        .macro_invocation_origins
        .items()
        .map(|(&expansion, origin)| {
            (
                expansion.expn_hash().local_hash().as_u64(),
                expansion,
                origin,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    for (_, expansion, origin) in origins {
        let local_definition = expansion
            .expn_data()
            .macro_def_id
            .and_then(|definition| definition.as_local());
        let mut observed = origin.selected_macro_rule;
        if omit_one_selection
            && origin.implementation_kind == MacroImplementationKind::Declarative
            && local_definition.is_some()
            && observed.is_some()
        {
            observed = None;
            omit_one_selection = false;
        }
        if origin.implementation_kind == MacroImplementationKind::Declarative
            && let Some(definition) = local_definition
        {
            let rules = definitions
                .get(&definition)
                .ok_or(SourceError::IncompleteMacroRuleObservation)?;
            let selection = observed.ok_or(SourceError::IncompleteMacroRuleObservation)?;
            if selection.definition != definition || selection.rule_index >= rules.len() {
                return Err(SourceError::IncompleteMacroRuleObservation);
            }
            selected
                .get_mut(&definition.local_def_index.as_u32())
                .ok_or(SourceError::IncompleteMacroRuleObservation)?
                .push(selection.rule_index);
        } else if observed.is_some() {
            return Err(SourceError::IncompleteMacroRuleObservation);
        }
    }
    if omit_one_selection {
        return Err(SourceError::IncompleteMacroRuleObservation);
    }

    let mut observations = Vec::new();
    for (_, definition, rules) in ordered_definitions {
        let mut selected_rule_indices = selected
            .remove(&definition.local_def_index.as_u32())
            .ok_or(SourceError::IncompleteMacroRuleObservation)?;
        selected_rule_indices.sort_unstable();
        if resolutions.expn_that_defined.contains_key(&definition) {
            continue;
        }
        let definition_span = tcx.def_span(definition);
        let definition_range = original_span_range(compiler, &inventory.offsets, definition_span)?;
        if opaque_anchors
            .iter()
            .any(|anchor| anchor.contains(definition_range))
        {
            continue;
        }
        if definition_span.from_expansion() {
            return Err(SourceError::IncompleteMacroRuleObservation);
        }
        let mut rule_ranges = Vec::with_capacity(rules.len());
        for rule in rules {
            if rule.start_span.from_expansion() || rule.end_span.from_expansion() {
                return Err(SourceError::IncompleteMacroRuleObservation);
            }
            let start = original_span_range(compiler, &inventory.offsets, rule.start_span)?;
            let end = original_span_range(compiler, &inventory.offsets, rule.end_span)?;
            if start.start >= end.end {
                return Err(SourceError::IncompleteMacroRuleObservation);
            }
            rule_ranges.push(ByteRange {
                start: start.start,
                end: end.end,
            });
        }
        let mut definition_range = definition_range;
        for rule in &rule_ranges {
            definition_range.start = definition_range.start.min(rule.start);
            definition_range.end = definition_range.end.max(rule.end);
        }
        observations.push(ObservedMacroRules {
            definition_range,
            rule_ranges,
            selected_rule_indices,
        });
    }
    if !selected.is_empty() {
        return Err(SourceError::IncompleteMacroRuleObservation);
    }
    refine_macro_rules_outside_opaque_anchors(inventory, observations, &opaque_anchors)?;
    merge_procedural_macro_atomic_groups(inventory, &opaque_anchors)
}

#[cfg(rust_item_dependencies_patched)]
fn collect_procedural_macro_observations(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &SourceInventory,
) -> Result<Vec<ObservedProceduralMacro>, SourceError> {
    let resolutions = tcx.resolutions(());
    let origin_map = &resolutions.macro_invocation_origins;
    let origins = origin_map
        .items()
        .map(|(&expansion, origin)| {
            (
                expansion.expn_hash().local_hash().as_u64(),
                expansion,
                origin,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    let mut observations = Vec::new();
    for (_, expansion, origin) in origins {
        if origin.implementation_kind != MacroImplementationKind::Procedural {
            continue;
        }

        let data = expansion.expn_data();
        let ExpnKind::Macro(kind, _) = data.kind else {
            return Err(SourceError::IncompleteProceduralMacroObservation);
        };
        let observation = match kind {
            MacroKind::Bang if origin.discovered_in_expansion == ExpnId::root() => {
                ObservedProceduralMacro::Invocation {
                    invocation_range: original_span_range(
                        compiler,
                        &inventory.offsets,
                        data.call_site,
                    )?,
                    node_range: original_span_range(
                        compiler,
                        &inventory.offsets,
                        origin.invocation_node_span,
                    )?,
                }
            }
            MacroKind::Attr | MacroKind::Derive => {
                let container = if kind == MacroKind::Attr
                    && origin.discovered_in_expansion == ExpnId::root()
                {
                    Some((expansion, origin))
                } else {
                    written_builtin_attribute_ancestor(origin_map, origin.discovered_in_expansion)?
                };
                let Some((container, container_origin)) = container else {
                    continue;
                };
                let target_range = original_span_range(
                    compiler,
                    &inventory.offsets,
                    container_origin
                        .target_span
                        .ok_or(SourceError::IncompleteProceduralMacroObservation)?,
                )?;
                ObservedProceduralMacro::Target {
                    invocation_range: original_span_range(
                        compiler,
                        &inventory.offsets,
                        container.expn_data().call_site,
                    )?,
                    node_range: original_span_range(
                        compiler,
                        &inventory.offsets,
                        container_origin.invocation_node_span,
                    )?,
                    target_range,
                }
            }
            MacroKind::Bang => continue,
        };
        observations.push(observation);
    }
    Ok(observations)
}

#[cfg(rust_item_dependencies_patched)]
fn written_builtin_attribute_ancestor<'a>(
    origins: &'a UnordMap<ExpnId, MacroInvocationOrigin>,
    mut expansion: ExpnId,
) -> Result<Option<(ExpnId, &'a MacroInvocationOrigin)>, SourceError> {
    while expansion != ExpnId::root() {
        let origin = origins
            .get(&expansion)
            .ok_or(SourceError::IncompleteProceduralMacroObservation)?;
        if origin.implementation_kind != MacroImplementationKind::Builtin
            || !matches!(
                expansion.expn_data().kind,
                ExpnKind::Macro(MacroKind::Attr, _)
            )
        {
            return Ok(None);
        }
        if origin.discovered_in_expansion == ExpnId::root() {
            return Ok(Some((expansion, origin)));
        }
        expansion = origin.discovered_in_expansion;
    }
    Err(SourceError::IncompleteProceduralMacroObservation)
}

fn resolve_procedural_macro_anchors(
    inventory: &SourceInventory,
    observations: Vec<ObservedProceduralMacro>,
) -> Result<BTreeSet<ByteRange>, SourceError> {
    validate_inventory(&inventory.original, &inventory.units, &inventory.pieces)?;
    validate_ownerless_attribute_invocations(
        &inventory.units,
        &inventory.ownerless_attribute_invocations,
    )?;

    let mut anchors = BTreeSet::new();
    for observation in observations {
        let anchor = match observation {
            ObservedProceduralMacro::Invocation {
                invocation_range,
                node_range,
            } => resolve_bang_macro_source(inventory, invocation_range, node_range)?,
            ObservedProceduralMacro::Target {
                invocation_range,
                node_range,
                target_range,
            } => {
                let source =
                    resolve_attribute_source(inventory, invocation_range, node_range, target_range)
                        .map_err(|_| SourceError::IncompleteProceduralMacroObservation)?;
                source
                    .invocation
                    .ok_or(SourceError::IncompleteProceduralMacroObservation)?;
                source.target
            }
        };
        anchors.insert(
            inventory
                .units
                .get(anchor.0 as usize)
                .ok_or(SourceError::IncompleteProceduralMacroObservation)?
                .full_range,
        );
    }
    Ok(anchors)
}

fn merge_procedural_macro_atomic_groups(
    inventory: &mut SourceInventory,
    anchors: &BTreeSet<ByteRange>,
) -> Result<(), SourceError> {
    validate_inventory(&inventory.original, &inventory.units, &inventory.pieces)?;
    validate_macro_rule_facts(&inventory.units, &inventory.macro_rules)?;
    validate_ownerless_attribute_invocations(
        &inventory.units,
        &inventory.ownerless_attribute_invocations,
    )?;

    let mut representatives = inventory
        .units
        .iter()
        .map(|unit| (unit.atomic_group, unit.atomic_group))
        .collect::<BTreeMap<_, _>>();
    for &anchor_range in anchors {
        inventory
            .units
            .iter()
            .find(|unit| unit.full_range == anchor_range)
            .ok_or(SourceError::IncompleteProceduralMacroObservation)?;
        let components = inventory
            .units
            .iter()
            .filter(|unit| anchor_range.contains(unit.full_range))
            .map(|unit| representatives[&unit.atomic_group])
            .collect::<BTreeSet<_>>();
        let representative = components
            .first()
            .copied()
            .ok_or(SourceError::IncompleteProceduralMacroObservation)?;
        for current in representatives.values_mut() {
            if components.contains(current) {
                *current = representative;
            }
        }
    }
    for unit in &mut inventory.units {
        unit.atomic_group = representatives[&unit.atomic_group];
    }

    validate_ownerless_attribute_invocations(
        &inventory.units,
        &inventory.ownerless_attribute_invocations,
    )?;
    Ok(())
}

fn resolve_bang_macro_source(
    inventory: &SourceInventory,
    invocation_range: ByteRange,
    node_range: ByteRange,
) -> Result<SourceUnitId, SourceError> {
    if invocation_range.is_empty() || !node_range.contains(invocation_range) {
        return Err(SourceError::IncompleteProceduralMacroObservation);
    }
    let mut candidates = inventory
        .units
        .iter()
        .filter(|unit| {
            unit.kind == WrittenUnitKind::MacroInvocation
                && unit.cfg_state == CfgState::Active
                && unit.full_range.contains(invocation_range)
                && unit.full_range.contains(node_range)
        })
        .collect::<Vec<_>>();
    let smallest = candidates
        .iter()
        .map(|unit| unit.full_range.len())
        .min()
        .ok_or(SourceError::IncompleteProceduralMacroObservation)?;
    candidates.retain(|unit| unit.full_range.len() == smallest);
    let [invocation] = candidates.as_slice() else {
        return Err(SourceError::IncompleteProceduralMacroObservation);
    };
    Ok(invocation.id)
}

fn valid_source_range(source: &str, range: ByteRange) -> bool {
    range.start <= range.end
        && range.end as usize <= source.len()
        && source.is_char_boundary(range.start as usize)
        && source.is_char_boundary(range.end as usize)
}

pub(crate) fn validate_macro_rule_facts(
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
) -> Result<(), SourceError> {
    let mut definitions = BTreeSet::new();
    let mut classified_rules = BTreeSet::new();
    for facts in macro_rules {
        let definition_id = facts.definition();
        let definition = units
            .get(definition_id.0 as usize)
            .ok_or(SourceError::InvalidInventory)?;
        if definition.kind != WrittenUnitKind::MacroDefinition
            || definition.cfg_state != CfgState::Active
            || !definitions.insert(definition.id)
        {
            return Err(SourceError::InvalidInventory);
        }

        match facts {
            MacroRuleSourceFacts::Whole { .. } => {}
            MacroRuleSourceFacts::Refined {
                rules,
                observed_selections,
                ..
            } => {
                let unique_rules = rules.iter().copied().collect::<BTreeSet<_>>();
                let unique_observed = observed_selections.iter().copied().collect::<BTreeSet<_>>();
                if rules.is_empty()
                    || unique_rules.len() != rules.len()
                    || !unique_observed.is_subset(&unique_rules)
                    || observed_selections.windows(2).any(|pair| pair[0] > pair[1])
                {
                    return Err(SourceError::InvalidInventory);
                }
                for rule in unique_rules {
                    let unit = units
                        .get(rule.0 as usize)
                        .ok_or(SourceError::InvalidInventory)?;
                    if unit.kind != WrittenUnitKind::MacroRule
                        || unit.cfg_state != CfgState::Active
                        || unit.parent != Some(definition.id)
                        || !classified_rules.insert(rule)
                    {
                        return Err(SourceError::InvalidInventory);
                    }
                }
            }
        }
    }
    let expected = units
        .iter()
        .filter(|unit| unit.kind == WrittenUnitKind::MacroRule)
        .map(|unit| unit.id)
        .collect::<BTreeSet<_>>();
    if classified_rules != expected {
        return Err(SourceError::InvalidInventory);
    }
    let expected_definitions = units
        .iter()
        .filter(|unit| {
            unit.kind == WrittenUnitKind::MacroDefinition && unit.cfg_state == CfgState::Active
        })
        .map(|unit| unit.id)
        .collect::<BTreeSet<_>>();
    if definitions != expected_definitions {
        return Err(SourceError::InvalidInventory);
    }
    Ok(())
}

pub(crate) fn validate_ownerless_attribute_invocations(
    units: &[WrittenUnit],
    invocations: &[SourceUnitId],
) -> Result<(), SourceError> {
    if invocations.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceError::InvalidInventory);
    }
    let mut targets = BTreeMap::<SourceUnitId, BTreeSet<SourceUnitId>>::new();
    for &invocation_id in invocations {
        let invocation = units
            .get(invocation_id.0 as usize)
            .ok_or(SourceError::InvalidInventory)?;
        let target_id = invocation.parent.ok_or(SourceError::InvalidInventory)?;
        let target = units
            .get(target_id.0 as usize)
            .ok_or(SourceError::InvalidInventory)?;
        if invocation.kind != WrittenUnitKind::MacroInvocation
            || invocation.cfg_state != CfgState::Active
            || invocation.parent != Some(target.id)
            || invocation.atomic_group != target.atomic_group
            || target.cfg_state != CfgState::Active
            || !matches!(
                target.kind,
                WrittenUnitKind::MacroInvocation
                    | WrittenUnitKind::Item
                    | WrittenUnitKind::NestedItem
                    | WrittenUnitKind::InlineModule
            )
        {
            return Err(SourceError::InvalidInventory);
        }
        if target.kind != WrittenUnitKind::MacroInvocation {
            targets.entry(target.id).or_default().insert(invocation.id);
        }
    }
    for (target, allowed) in targets {
        if units.iter().any(|unit| {
            unit.parent == Some(target) && !allowed.contains(&unit.id)
                || unit.parent.is_some_and(|parent| allowed.contains(&parent))
        }) {
            return Err(SourceError::InvalidInventory);
        }
    }
    Ok(())
}

pub(crate) fn original_span_range(
    compiler: &Compiler,
    offsets: &OriginalOffsetMap,
    span: Span,
) -> Result<ByteRange, SourceError> {
    if span.is_dummy() {
        return Err(SourceError::InvalidSpan);
    }
    let source_map = compiler.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos || start.sf.name.short().to_string() != "main.rs" {
        return Err(SourceError::InvalidSpan);
    }
    offsets.original_range(ByteRange {
        start: start.pos.0,
        end: end.pos.0,
    })
}

fn main_source_file(
    compiler: &Compiler,
    krate: &ast::Crate,
) -> Result<Arc<SourceFile>, SourceError> {
    let source_map = compiler.sess.source_map();
    let source_file = source_map.lookup_source_file(krate.spans.inner_span.lo());
    if source_file.name.short().to_string() != "main.rs" {
        return Err(SourceError::InvalidSpan);
    }
    Ok(source_file)
}

struct UnitCollector<'a> {
    compiler: &'a Compiler,
    source_file: Arc<SourceFile>,
    offsets: &'a OriginalOffsetMap,
    features: Features,
    units: Vec<PendingUnit>,
    parent_stack: Vec<u32>,
    active_stack: Vec<bool>,
    body_depth: u32,
    seen_macro_ranges: BTreeMap<ByteRange, u32>,
    next_syntax_ordinal: u32,
    error: Option<SourceError>,
}

impl<'a> UnitCollector<'a> {
    fn new(
        compiler: &'a Compiler,
        source_file: Arc<SourceFile>,
        offsets: &'a OriginalOffsetMap,
        features: Features,
        root_active: bool,
        original_len: usize,
    ) -> Result<Self, SourceError> {
        let original_len = u32::try_from(original_len).map_err(|_| SourceError::SourceTooLarge)?;
        Ok(Self {
            compiler,
            source_file,
            offsets,
            features,
            units: vec![PendingUnit {
                temporary_id: 0,
                kind: WrittenUnitKind::CrateRoot,
                full_range: ByteRange {
                    start: 0,
                    end: original_len,
                },
                parent: None,
                cfg_state: if root_active {
                    CfgState::Active
                } else {
                    CfgState::Inactive
                },
                atomic_representative: 0,
                syntax_ordinal: 0,
            }],
            parent_stack: vec![0],
            active_stack: vec![root_active],
            body_depth: 0,
            seen_macro_ranges: BTreeMap::new(),
            next_syntax_ordinal: 1,
            error: None,
        })
    }

    fn finish(mut self) -> Result<Vec<WrittenUnit>, SourceError> {
        if let Some(error) = self.error.take() {
            return Err(error);
        }
        finish_pending_units(self.units).map(|(units, _)| units)
    }

    fn current_parent(&self) -> u32 {
        *self
            .parent_stack
            .last()
            .expect("crate root parent must exist")
    }

    fn current_active(&self) -> bool {
        *self
            .active_stack
            .last()
            .expect("crate root cfg state must exist")
    }

    fn fail(&mut self, error: SourceError) {
        if self.error.is_none() {
            self.error = Some(error);
        }
    }

    fn node_is_active<T: ast::HasTokens + Clone>(&self, node: &T) -> bool {
        self.configured(node).is_some()
    }

    fn configured<T: ast::HasTokens + Clone>(&self, node: &T) -> Option<T> {
        if !self.current_active() {
            return None;
        }
        StripUnconfigured {
            sess: &self.compiler.sess,
            features: Some(&self.features),
            config_tokens: false,
            lint_node_id: ast::CRATE_NODE_ID,
        }
        .configure(node.clone())
    }

    fn record_configured_attribute_macros(
        &mut self,
        original: &[ast::Attribute],
        configured: &[ast::Attribute],
        active: bool,
    ) {
        struct AttributeMacroCollector<'a, 'b> {
            units: &'a mut UnitCollector<'b>,
            active: bool,
        }

        impl<'ast> Visitor<'ast> for AttributeMacroCollector<'_, '_> {
            fn visit_expr(&mut self, expression: &'ast ast::Expr) {
                if let ast::ExprKind::MacCall(call) = &expression.kind
                    && let Err(error) = self.units.record_macro(
                        call.span(),
                        self.active,
                        Some(expression.span),
                        None,
                    )
                {
                    self.units.fail(error);
                }
                visit::walk_expr(self, expression);
            }
        }

        let mut collector = AttributeMacroCollector {
            units: self,
            active,
        };
        for attribute in configured {
            if original.iter().any(|written| written.id == attribute.id) {
                continue;
            }
            if let ast::AttrKind::Normal(normal) = &attribute.kind
                && let ast::AttrArgs::Eq { expr, .. } = &normal.item.args
            {
                collector.visit_expr(expr);
            }
        }
    }

    fn span_range(&self, span: Span) -> Result<ByteRange, SourceError> {
        if span.is_dummy() {
            return Err(SourceError::InvalidSpan);
        }
        let source_map = self.compiler.sess.source_map();
        let start = source_map.lookup_byte_offset(span.lo());
        let end = source_map.lookup_byte_offset(span.hi());
        if start.sf.start_pos != self.source_file.start_pos
            || end.sf.start_pos != self.source_file.start_pos
        {
            return Err(SourceError::InvalidSpan);
        }
        self.offsets.original_range(ByteRange {
            start: start.pos.0,
            end: end.pos.0,
        })
    }

    fn add_unit(
        &mut self,
        kind: WrittenUnitKind,
        range: ByteRange,
        active: bool,
        parent: u32,
        atomic_representative: Option<u32>,
    ) -> u32 {
        let temporary_id = self.units.len() as u32;
        let representative = atomic_representative.unwrap_or(temporary_id);
        self.units.push(PendingUnit {
            temporary_id,
            kind,
            full_range: range,
            parent: Some(parent),
            cfg_state: if active {
                CfgState::Active
            } else {
                CfgState::Inactive
            },
            atomic_representative: representative,
            syntax_ordinal: self.next_syntax_ordinal,
        });
        self.next_syntax_ordinal += 1;
        temporary_id
    }

    fn record_macro(
        &mut self,
        span: Span,
        active: bool,
        full_span: Option<Span>,
        atomic_representative: Option<u32>,
    ) -> Result<u32, SourceError> {
        let key = self.span_range(span)?;
        if let Some(&existing) = self.seen_macro_ranges.get(&key) {
            return Ok(existing);
        }
        let range = self.span_range(full_span.unwrap_or(span))?;
        let id = self.add_unit(
            WrittenUnitKind::MacroInvocation,
            range,
            active,
            self.current_parent(),
            atomic_representative.or_else(|| self.parent_stack.last().copied()),
        );
        self.seen_macro_ranges.insert(key, id);
        Ok(id)
    }

    fn collect_use_leaves(
        &mut self,
        tree: &ast::UseTree,
        parent: u32,
        active: bool,
    ) -> Result<(), SourceError> {
        match &tree.kind {
            ast::UseTreeKind::Nested { items, .. } => {
                for (nested, _) in items {
                    self.collect_use_leaves(nested, parent, active)?;
                }
            }
            ast::UseTreeKind::Simple(_) | ast::UseTreeKind::Glob(_) => {
                let range = self.span_range(tree.span())?;
                self.add_unit(WrittenUnitKind::UseLeaf, range, active, parent, None);
            }
        }
        Ok(())
    }
}

fn finish_pending_units(
    mut units: Vec<PendingUnit>,
) -> Result<(Vec<WrittenUnit>, BTreeMap<u32, SourceUnitId>), SourceError> {
    units.sort_by_key(|unit| {
        (
            unit.full_range.start,
            std::cmp::Reverse(unit.full_range.end),
            unit.kind.rank(),
            unit.syntax_ordinal,
        )
    });

    let mut id_map = BTreeMap::new();
    for (index, unit) in units.iter().enumerate() {
        id_map.insert(unit.temporary_id, SourceUnitId(index as u32));
    }
    let mut group_representatives = units
        .iter()
        .map(|unit| unit.atomic_representative)
        .collect::<Vec<_>>();
    group_representatives.sort_by_key(|temporary| id_map[temporary]);
    group_representatives.dedup();
    let group_map = group_representatives
        .into_iter()
        .enumerate()
        .map(|(index, temporary)| (temporary, AtomicGroupId(index as u32)))
        .collect::<BTreeMap<_, _>>();

    let mut role_ordinals = BTreeMap::<WrittenUnitKind, u32>::new();
    let written = units
        .into_iter()
        .enumerate()
        .map(|(index, unit)| {
            let same_role_ordinal = role_ordinals.entry(unit.kind).or_default();
            let ordinal = *same_role_ordinal;
            *same_role_ordinal += 1;
            Ok(WrittenUnit {
                id: SourceUnitId(index as u32),
                kind: unit.kind,
                full_range: unit.full_range,
                parent: unit.parent.map(|parent| id_map[&parent]),
                cfg_state: unit.cfg_state,
                atomic_group: group_map[&unit.atomic_representative],
                same_role_ordinal: ordinal,
            })
        })
        .collect::<Result<Vec<_>, SourceError>>()?;
    Ok((written, id_map))
}

impl<'ast> Visitor<'ast> for UnitCollector<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let configured = self.configured(item);
        let active = configured.is_some();
        let range = match self.span_range(item.span_with_attributes()) {
            Ok(range) => range,
            Err(error) => {
                self.fail(error);
                return;
            }
        };
        let kind = match &item.kind {
            ast::ItemKind::Mod(_, _, ast::ModKind::Loaded(_, ast::Inline::Yes, _)) => {
                WrittenUnitKind::InlineModule
            }
            ast::ItemKind::Use(_) => WrittenUnitKind::UseItem,
            ast::ItemKind::MacroDef(..) => WrittenUnitKind::MacroDefinition,
            ast::ItemKind::MacCall(_) => WrittenUnitKind::MacroInvocation,
            _ if self.body_depth > 0 => WrittenUnitKind::NestedItem,
            _ => WrittenUnitKind::Item,
        };
        let parent = self.current_parent();
        let id = self.add_unit(kind, range, active, parent, None);

        let mut derive_ranges = Vec::new();
        for attribute in item.attrs.iter().chain(
            configured
                .as_ref()
                .into_iter()
                .flat_map(|item| item.attrs.iter()),
        ) {
            if !attribute.has_name(sym::derive) {
                continue;
            }
            let written_span = item
                .attrs
                .iter()
                .filter(|written| written.span.contains(attribute.span))
                .min_by_key(|written| written.span.hi().0 - written.span.lo().0)
                .map_or(attribute.span, |written| written.span);
            match self.span_range(written_span) {
                Ok(attribute_range) => derive_ranges.push(attribute_range),
                Err(error) => self.fail(error),
            }
        }
        derive_ranges.sort();
        derive_ranges.dedup();
        for attribute_range in derive_ranges {
            self.add_unit(
                WrittenUnitKind::MacroInvocation,
                attribute_range,
                active,
                id,
                Some(id),
            );
        }

        if let ast::ItemKind::MacCall(mac) = &item.kind {
            match self.span_range(mac.span()) {
                Ok(key) => {
                    self.seen_macro_ranges.insert(key, id);
                }
                Err(error) => self.fail(error),
            }
        }
        if let ast::ItemKind::Use(tree) = &item.kind
            && let Err(error) = self.collect_use_leaves(tree, id, active)
        {
            self.fail(error);
        }

        self.parent_stack.push(id);
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(item.attrs(), configured.attrs(), active);
        }
        visit::walk_item(self, item);
        self.active_stack.pop();
        self.parent_stack.pop();
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: AssocCtxt) {
        let configured = self.configured(item);
        let active = configured.is_some();
        let span = item
            .attrs
            .iter()
            .fold(item.span, |span, attribute| span.to(attribute.span));
        let range = match self.span_range(span) {
            Ok(range) => range,
            Err(error) => {
                self.fail(error);
                return;
            }
        };
        let kind = if matches!(item.kind, ast::AssocItemKind::MacCall(_)) {
            WrittenUnitKind::MacroInvocation
        } else {
            match context {
                AssocCtxt::Trait => WrittenUnitKind::TraitMember,
                AssocCtxt::Impl { .. } => WrittenUnitKind::ImplMember,
            }
        };
        let parent = self.current_parent();
        let id = self.add_unit(kind, range, active, parent, None);
        if let ast::AssocItemKind::MacCall(mac) = &item.kind {
            match self.span_range(mac.span()) {
                Ok(key) => {
                    self.seen_macro_ranges.insert(key, id);
                }
                Err(error) => self.fail(error),
            }
        }

        self.parent_stack.push(id);
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(item.attrs(), configured.attrs(), active);
        }
        visit::walk_assoc_item(self, item, context);
        self.active_stack.pop();
        self.parent_stack.pop();
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        let configured = self.configured(item);
        let active = configured.is_some();
        let span = item
            .attrs
            .iter()
            .fold(item.span, |span, attribute| span.to(attribute.span));
        let range = match self.span_range(span) {
            Ok(range) => range,
            Err(error) => {
                self.fail(error);
                return;
            }
        };
        let kind = if matches!(item.kind, ast::ForeignItemKind::MacCall(_)) {
            WrittenUnitKind::MacroInvocation
        } else {
            WrittenUnitKind::Item
        };
        let parent = self.current_parent();
        let id = self.add_unit(kind, range, active, parent, None);
        if let ast::ForeignItemKind::MacCall(mac) = &item.kind {
            match self.span_range(mac.span()) {
                Ok(key) => {
                    self.seen_macro_ranges.insert(key, id);
                }
                Err(error) => self.fail(error),
            }
        }

        self.parent_stack.push(id);
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(item.attrs(), configured.attrs(), active);
        }
        visit::walk_item(self, item);
        self.active_stack.pop();
        self.parent_stack.pop();
    }

    fn visit_block(&mut self, block: &'ast ast::Block) {
        self.body_depth += 1;
        visit::walk_block(self, block);
        self.body_depth -= 1;
    }

    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        let configured = self.configured(statement);
        let active = configured.is_some();
        if let ast::StmtKind::MacCall(call) = &statement.kind
            && let Err(error) =
                self.record_macro(call.mac.span(), active, Some(statement.span), None)
        {
            self.fail(error);
        }
        self.active_stack.push(active);
        if let Some(configured) = &configured
            && !matches!(&statement.kind, ast::StmtKind::Item(_))
        {
            self.record_configured_attribute_macros(statement.attrs(), configured.attrs(), active);
        }
        visit::walk_stmt(self, statement);
        self.active_stack.pop();
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        let configured = self.configured(expression);
        let active = configured.is_some();
        if let ast::ExprKind::MacCall(call) = &expression.kind
            && let Err(error) = self.record_macro(call.span(), active, Some(expression.span), None)
        {
            self.fail(error);
        }
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(expression.attrs(), configured.attrs(), active);
        }
        visit::walk_expr(self, expression);
        self.active_stack.pop();
    }

    fn visit_arm(&mut self, arm: &'ast ast::Arm) {
        let configured = self.configured(arm);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(arm.attrs(), configured.attrs(), active);
        }
        visit::walk_arm(self, arm);
        self.active_stack.pop();
    }

    fn visit_expr_field(&mut self, field: &'ast ast::ExprField) {
        let configured = self.configured(field);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(field.attrs(), configured.attrs(), active);
        }
        visit::walk_expr_field(self, field);
        self.active_stack.pop();
    }

    fn visit_field_def(&mut self, field: &'ast ast::FieldDef) {
        let configured = self.configured(field);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(field.attrs(), configured.attrs(), active);
        }
        visit::walk_field_def(self, field);
        self.active_stack.pop();
    }

    fn visit_generic_param(&mut self, parameter: &'ast ast::GenericParam) {
        let configured = self.configured(parameter);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(parameter.attrs(), configured.attrs(), active);
        }
        visit::walk_generic_param(self, parameter);
        self.active_stack.pop();
    }

    fn visit_param(&mut self, parameter: &'ast ast::Param) {
        let configured = self.configured(parameter);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(parameter.attrs(), configured.attrs(), active);
        }
        visit::walk_param(self, parameter);
        self.active_stack.pop();
    }

    fn visit_pat_field(&mut self, field: &'ast ast::PatField) {
        let configured = self.configured(field);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(field.attrs(), configured.attrs(), active);
        }
        visit::walk_pat_field(self, field);
        self.active_stack.pop();
    }

    fn visit_variant(&mut self, variant: &'ast ast::Variant) {
        let configured = self.configured(variant);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(variant.attrs(), configured.attrs(), active);
        }
        visit::walk_variant(self, variant);
        self.active_stack.pop();
    }

    fn visit_where_predicate(&mut self, predicate: &'ast ast::WherePredicate) {
        let configured = self.configured(predicate);
        let active = configured.is_some();
        self.active_stack.push(active);
        if let Some(configured) = &configured {
            self.record_configured_attribute_macros(predicate.attrs(), configured.attrs(), active);
        }
        visit::walk_where_predicate(self, predicate);
        self.active_stack.pop();
    }

    fn visit_mac_call(&mut self, call: &'ast ast::MacCall) {
        if let Err(error) = self.record_macro(call.span(), self.current_active(), None, None) {
            self.fail(error);
        }
    }
}

fn own_lexical_pieces(source: &str, units: &[WrittenUnit]) -> Result<Vec<OwnedPiece>, SourceError> {
    let mut raw = Vec::new();
    let mut base = 0_u32;
    let mut input = source;
    if source.as_bytes().starts_with(&[0xef, 0xbb, 0xbf]) {
        raw.push((ByteRange { start: 0, end: 3 }, PieceKind::Trivia));
        base = 3;
        input = &source[3..];
    }

    if let Some(length) = strip_shebang(input) {
        let length = u32::try_from(length).map_err(|_| SourceError::SourceTooLarge)?;
        let end = base
            .checked_add(length)
            .ok_or(SourceError::SourceTooLarge)?;
        raw.push((ByteRange { start: base, end }, PieceKind::Trivia));
        base = end;
        input = &input[length as usize..];
    }

    let mut offset = base;
    for token in tokenize(input, FrontmatterAllowed::Yes) {
        let end = offset
            .checked_add(token.len)
            .ok_or(SourceError::SourceTooLarge)?;
        let kind = match token.kind {
            TokenKind::Whitespace
            | TokenKind::LineComment { doc_style: None }
            | TokenKind::BlockComment {
                doc_style: None, ..
            } => PieceKind::Trivia,
            _ => PieceKind::Token,
        };
        let token_range = ByteRange { start: offset, end };
        let token_bytes = &source.as_bytes()[offset as usize..end as usize];
        if matches!(token.kind, TokenKind::LineComment { .. }) && token_bytes.ends_with(b"\r") {
            let comment_kind = if matches!(token.kind, TokenKind::LineComment { doc_style: None }) {
                PieceKind::Trivia
            } else {
                PieceKind::Token
            };
            raw.push((
                ByteRange {
                    start: offset,
                    end: end - 1,
                },
                comment_kind,
            ));
            raw.push((
                ByteRange {
                    start: end - 1,
                    end,
                },
                PieceKind::Trivia,
            ));
        } else if matches!(token.kind, TokenKind::Whitespace)
            && token_bytes.starts_with(b"\n")
            && raw.last().is_some_and(|(range, piece_kind)| {
                *piece_kind == PieceKind::Trivia
                    && range.end == offset
                    && &source.as_bytes()[range.start as usize..range.end as usize] == b"\r"
            })
        {
            raw.last_mut().expect("the CR trivia was checked").0.end += 1;
            if end > offset + 1 {
                raw.push((
                    ByteRange {
                        start: offset + 1,
                        end,
                    },
                    PieceKind::Trivia,
                ));
            }
        } else {
            raw.push((token_range, kind));
        }
        offset = end;
    }
    if offset != source.len() as u32 {
        return Err(SourceError::InvalidInventory);
    }

    let depths = unit_depths(units)?;
    raw.into_iter()
        .map(|(range, kind)| {
            let owner = units
                .iter()
                .filter(|unit| unit.full_range.contains(range))
                .max_by_key(|unit| {
                    (
                        depths[unit.id.0 as usize],
                        std::cmp::Reverse(unit.full_range.len()),
                        unit.kind.rank(),
                        std::cmp::Reverse(unit.id),
                    )
                })
                .ok_or(SourceError::InvalidInventory)?
                .id;
            Ok(OwnedPiece { range, owner, kind })
        })
        .collect()
}

fn unit_depths(units: &[WrittenUnit]) -> Result<Vec<u32>, SourceError> {
    let mut depths = vec![None; units.len()];
    for unit in units {
        let mut depth = 0_u32;
        let mut cursor = unit.parent;
        let mut seen = 0_usize;
        while let Some(parent) = cursor {
            let parent = units
                .get(parent.0 as usize)
                .ok_or(SourceError::InvalidInventory)?;
            depth += 1;
            cursor = parent.parent;
            seen += 1;
            if seen > units.len() {
                return Err(SourceError::InvalidInventory);
            }
        }
        depths[unit.id.0 as usize] = Some(depth);
    }
    depths
        .into_iter()
        .map(|depth| depth.ok_or(SourceError::InvalidInventory))
        .collect()
}

fn validate_inventory(
    original: &str,
    units: &[WrittenUnit],
    pieces: &[OwnedPiece],
) -> Result<(), SourceError> {
    let original_len = u32::try_from(original.len()).map_err(|_| SourceError::SourceTooLarge)?;
    let roots = units
        .iter()
        .filter(|unit| unit.parent.is_none())
        .collect::<Vec<_>>();
    if roots.len() != 1
        || roots[0].kind != WrittenUnitKind::CrateRoot
        || roots[0].full_range
            != (ByteRange {
                start: 0,
                end: original_len,
            })
    {
        return Err(SourceError::InvalidInventory);
    }
    for (index, unit) in units.iter().enumerate() {
        if unit.id != SourceUnitId(index as u32)
            || unit.full_range.start > unit.full_range.end
            || unit.full_range.end > original_len
            || !original.is_char_boundary(unit.full_range.start as usize)
            || !original.is_char_boundary(unit.full_range.end as usize)
        {
            return Err(SourceError::InvalidInventory);
        }
        if let Some(parent) = unit.parent {
            let parent = units
                .get(parent.0 as usize)
                .ok_or(SourceError::InvalidInventory)?;
            if !parent.full_range.contains(unit.full_range) {
                return Err(SourceError::InvalidInventory);
            }
            if parent.cfg_state == CfgState::Inactive && unit.cfg_state != CfgState::Inactive {
                return Err(SourceError::InvalidInventory);
            }
        }
    }
    let _ = unit_depths(units)?;

    let mut cursor = 0_u32;
    for piece in pieces {
        if piece.range.start != cursor
            || piece.range.start >= piece.range.end
            || piece.range.end > original_len
            || !original.is_char_boundary(piece.range.start as usize)
            || !original.is_char_boundary(piece.range.end as usize)
            || units
                .get(piece.owner.0 as usize)
                .is_none_or(|owner| !owner.full_range.contains(piece.range))
        {
            return Err(SourceError::InvalidInventory);
        }
        cursor = piece.range.end;
    }
    if cursor != original_len {
        return Err(SourceError::InvalidInventory);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use super::{
        AtomicGroupId, ByteRange, CfgState, MacroRuleSourceFacts, ObservedMacroRules,
        ObservedProceduralMacro, OriginalOffsetMap, PieceKind, SourceError, SourceInventory,
        SourceUnitId, WrittenUnit, WrittenUnitKind, merge_procedural_macro_atomic_groups,
        own_lexical_pieces, refine_macro_rules, refine_macro_rules_outside_opaque_anchors,
        resolve_procedural_macro_anchors, validate_macro_rule_facts,
    };
    use crate::rewrite::rewrite_source;

    #[test]
    fn original_offsets_keep_distinct_left_and_right_preimages() {
        let source = "\u{feff}a\r\n日\r\n";
        let (normalized, offsets) = OriginalOffsetMap::from_source(source).unwrap();

        assert_eq!(normalized, "a\n日\n");
        assert_eq!(source.len(), 11);
        assert_eq!(
            (0..=offsets.normalized_len)
                .map(|position| offsets.left(position).unwrap())
                .collect::<Vec<_>>(),
            vec![0, 4, 5, 7, 8, 9, 10]
        );
        assert_eq!(
            (0..=offsets.normalized_len)
                .map(|position| offsets.right(position).unwrap())
                .collect::<Vec<_>>(),
            vec![3, 4, 6, 7, 8, 9, 11]
        );
        for (normalized, original) in [
            ((0, 1), (3, 4)),
            ((2, 5), (6, 9)),
            ((1, 2), (4, 5)),
            ((0, 0), (3, 3)),
            ((2, 2), (6, 6)),
            ((6, 6), (11, 11)),
        ] {
            assert_eq!(
                offsets
                    .original_range(ByteRange {
                        start: normalized.0,
                        end: normalized.1,
                    })
                    .unwrap(),
                ByteRange {
                    start: original.0,
                    end: original.1,
                }
            );
        }

        for original in 0..=offsets.original_len {
            let normalized = offsets.normalized_from_original(original).unwrap();
            assert!(offsets.left(normalized).unwrap() <= original);
            assert!(original <= offsets.right(normalized).unwrap());
        }
    }

    #[test]
    fn lexical_pieces_partition_removed_and_retained_bytes() {
        let source = Arc::<str>::from("\u{feff}a\r\n日\r\n");
        let root = WrittenUnit {
            id: SourceUnitId(0),
            kind: WrittenUnitKind::CrateRoot,
            full_range: ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            parent: None,
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(0),
            same_role_ordinal: 0,
        };

        let pieces = own_lexical_pieces(&source, &[root]).unwrap();
        assert_eq!(
            pieces
                .iter()
                .map(|piece| (piece.range, piece.kind))
                .collect::<Vec<_>>(),
            vec![
                (ByteRange { start: 0, end: 3 }, PieceKind::Trivia),
                (ByteRange { start: 3, end: 4 }, PieceKind::Token),
                (ByteRange { start: 4, end: 6 }, PieceKind::Trivia),
                (ByteRange { start: 6, end: 9 }, PieceKind::Token),
                (ByteRange { start: 9, end: 11 }, PieceKind::Trivia),
            ]
        );

        let source = Arc::<str>::from("/// documentation\r\nfn main() {}\r\n");
        let root = WrittenUnit {
            id: SourceUnitId(0),
            kind: WrittenUnitKind::CrateRoot,
            full_range: ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            parent: None,
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(0),
            same_role_ordinal: 0,
        };
        let pieces = own_lexical_pieces(&source, &[root]).unwrap();
        assert_eq!(
            &source[pieces[0].range.start as usize..pieces[0].range.end as usize],
            "/// documentation"
        );
        assert_eq!(pieces[0].kind, PieceKind::Token);
        assert_eq!(
            pieces
                .iter()
                .filter(|piece| {
                    &source[piece.range.start as usize..piece.range.end as usize] == "\r\n"
                })
                .count(),
            2
        );

        let source = Arc::<str>::from("#!/usr/bin/env rustx\nfn main() {}\n");
        let root = WrittenUnit {
            id: SourceUnitId(0),
            kind: WrittenUnitKind::CrateRoot,
            full_range: ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            parent: None,
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(0),
            same_role_ordinal: 0,
        };
        let pieces = own_lexical_pieces(&source, &[root]).unwrap();
        assert_eq!(pieces[0].kind, PieceKind::Trivia);
        assert_eq!(
            &source[pieces[0].range.start as usize..pieces[0].range.end as usize],
            "#!/usr/bin/env rustx"
        );
    }

    #[test]
    fn macro_rule_inventory_removes_only_unselected_complete_rules() {
        let source = Arc::<str>::from(
            "macro_rules! m { () => { 1 }; (@dead) => { 2 } }\nfn main(){let _=m!();}\n",
        );
        let definition = marker(&source, "macro_rules! m { () => { 1 }; (@dead) => { 2 } }");
        let first = marker(&source, "() => { 1 };");
        let second = marker(&source, "(@dead) => { 2 }");
        let (normalized, offsets) = OriginalOffsetMap::from_source(&source).unwrap();
        let units = vec![
            WrittenUnit {
                id: SourceUnitId(0),
                kind: WrittenUnitKind::CrateRoot,
                full_range: ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                parent: None,
                cfg_state: CfgState::Active,
                atomic_group: AtomicGroupId(0),
                same_role_ordinal: 0,
            },
            WrittenUnit {
                id: SourceUnitId(1),
                kind: WrittenUnitKind::MacroDefinition,
                full_range: definition,
                parent: Some(SourceUnitId(0)),
                cfg_state: CfgState::Active,
                atomic_group: AtomicGroupId(1),
                same_role_ordinal: 0,
            },
        ];
        let pieces = own_lexical_pieces(&source, &units).unwrap();
        let mut inventory = SourceInventory {
            original: Arc::clone(&source),
            normalized: Arc::from(normalized),
            offsets,
            units,
            pieces,
            macro_rules: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        };
        let mut unselected_inventory = inventory.clone();

        refine_macro_rules(
            &mut inventory,
            vec![ObservedMacroRules {
                definition_range: definition,
                rule_ranges: vec![first, second],
                selected_rule_indices: vec![0, 0],
            }],
        )
        .unwrap();

        let MacroRuleSourceFacts::Refined {
            definition: facts_definition,
            rules,
            observed_selections,
        } = &inventory.macro_rules[0]
        else {
            panic!("an observed definition must be refined")
        };
        assert_eq!(rules.len(), 2);
        assert_eq!(observed_selections.as_slice(), &[rules[0], rules[0]]);
        assert_eq!(inventory.units[rules[0].0 as usize].full_range, first);
        assert_eq!(inventory.units[rules[1].0 as usize].full_range, second);
        assert_ne!(
            inventory.units[rules[0].0 as usize].atomic_group,
            inventory.units[rules[1].0 as usize].atomic_group
        );

        let retained = BTreeSet::from([SourceUnitId(0), *facts_definition, rules[0]]);
        let rewrite = rewrite_source(&inventory, &retained).unwrap();
        assert_eq!(
            rewrite.source,
            "macro_rules! m { () => { 1 };  }\nfn main(){let _=m!();}\n"
        );
        assert!(rewrite.source.len() < source.len());
        assert_eq!(
            rewrite
                .pieces
                .iter()
                .map(|piece| {
                    &source[piece.original_range.start as usize..piece.original_range.end as usize]
                })
                .collect::<String>(),
            rewrite.source
        );

        refine_macro_rules(
            &mut unselected_inventory,
            vec![ObservedMacroRules {
                definition_range: definition,
                rule_ranges: vec![first, second],
                selected_rule_indices: Vec::new(),
            }],
        )
        .unwrap();
        let MacroRuleSourceFacts::Refined {
            rules,
            observed_selections,
            ..
        } = &unselected_inventory.macro_rules[0]
        else {
            panic!("an observed definition must be refined")
        };
        assert!(observed_selections.is_empty());
        assert_eq!(rules.len(), 2);
    }

    #[test]
    fn macro_rule_inventory_rejects_missing_definition_observation() {
        let source = Arc::<str>::from("macro_rules! m { () => {} }\n");
        let definition = marker(&source, "macro_rules! m { () => {} }");
        let (normalized, offsets) = OriginalOffsetMap::from_source(&source).unwrap();
        let units = vec![
            WrittenUnit {
                id: SourceUnitId(0),
                kind: WrittenUnitKind::CrateRoot,
                full_range: ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                parent: None,
                cfg_state: CfgState::Active,
                atomic_group: AtomicGroupId(0),
                same_role_ordinal: 0,
            },
            WrittenUnit {
                id: SourceUnitId(1),
                kind: WrittenUnitKind::MacroDefinition,
                full_range: definition,
                parent: Some(SourceUnitId(0)),
                cfg_state: CfgState::Active,
                atomic_group: AtomicGroupId(1),
                same_role_ordinal: 0,
            },
        ];
        let pieces = own_lexical_pieces(&source, &units).unwrap();
        let mut inventory = SourceInventory {
            original: source,
            normalized: Arc::from(normalized),
            offsets,
            units,
            pieces,
            macro_rules: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        };

        assert_eq!(
            refine_macro_rules(&mut inventory, Vec::new()),
            Err(SourceError::IncompleteMacroRuleObservation)
        );
    }

    #[test]
    fn procedural_bang_macro_merges_every_group_inside_its_invocation() {
        let source = Arc::<str>::from("outer!(inner!());\nfn untouched() {}\n");
        let outer = marker(&source, "outer!(inner!());");
        let inner = marker(&source, "inner!()");
        let untouched = marker(&source, "fn untouched() {}");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::MacroInvocation, outer, Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, inner, Some(1), 2),
            unit(3, WrittenUnitKind::Item, untouched, Some(0), 3),
        ];
        let mut inventory = test_inventory(source, units, Vec::new());
        let invocation_range = marker(&inventory.original, "outer!(inner!())");

        let anchors = resolve_procedural_macro_anchors(
            &inventory,
            vec![ObservedProceduralMacro::Invocation {
                invocation_range,
                node_range: outer,
            }],
        )
        .unwrap();
        merge_procedural_macro_atomic_groups(&mut inventory, &anchors).unwrap();

        assert_eq!(
            inventory.units[1].atomic_group,
            inventory.units[2].atomic_group
        );
        assert_ne!(
            inventory.units[0].atomic_group,
            inventory.units[1].atomic_group
        );
        assert_ne!(
            inventory.units[1].atomic_group,
            inventory.units[3].atomic_group
        );
    }

    #[test]
    fn procedural_attribute_keeps_nested_macro_rules_whole_and_merges_its_target() {
        let source = Arc::<str>::from(
            "#[cfg_attr(all(), wrap)]\nmod subject { macro_rules! local { (inside) => {} } }\nmacro_rules! outside { (outside) => {} }\n",
        );
        let target = marker(
            &source,
            "#[cfg_attr(all(), wrap)]\nmod subject { macro_rules! local { (inside) => {} } }",
        );
        let target_without_attribute = marker(
            &source,
            "mod subject { macro_rules! local { (inside) => {} } }",
        );
        let attribute = marker(&source, "#[cfg_attr(all(), wrap)]");
        let definition = marker(&source, "macro_rules! local { (inside) => {} }");
        let rule = marker(&source, "(inside) => {}");
        let outside_definition = marker(&source, "macro_rules! outside { (outside) => {} }");
        let outside_rule = marker(&source, "(outside) => {}");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::InlineModule, target, Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, attribute, Some(1), 1),
            unit(3, WrittenUnitKind::MacroDefinition, definition, Some(1), 2),
            unit(
                4,
                WrittenUnitKind::MacroDefinition,
                outside_definition,
                Some(0),
                3,
            ),
        ];
        let mut inventory = test_inventory(source, units, Vec::new());
        let anchors = resolve_procedural_macro_anchors(
            &inventory,
            vec![ObservedProceduralMacro::Target {
                invocation_range: attribute,
                node_range: target,
                target_range: target_without_attribute,
            }],
        )
        .unwrap();
        refine_macro_rules_outside_opaque_anchors(
            &mut inventory,
            vec![
                ObservedMacroRules {
                    definition_range: definition,
                    rule_ranges: vec![rule],
                    selected_rule_indices: vec![0],
                },
                ObservedMacroRules {
                    definition_range: outside_definition,
                    rule_ranges: vec![outside_rule],
                    selected_rule_indices: vec![0],
                },
            ],
            &anchors,
        )
        .unwrap();

        assert_eq!(inventory.macro_rules.len(), 2);
        let opaque_facts = inventory
            .macro_rules
            .iter()
            .find(|facts| inventory.units[facts.definition().0 as usize].full_range == definition)
            .unwrap();
        assert!(matches!(opaque_facts, MacroRuleSourceFacts::Whole { .. }));
        let outside_facts = inventory
            .macro_rules
            .iter()
            .find(|facts| {
                inventory.units[facts.definition().0 as usize].full_range == outside_definition
            })
            .unwrap();
        let MacroRuleSourceFacts::Refined {
            definition: outside_facts_definition,
            rules: outside_rules,
            ..
        } = outside_facts
        else {
            panic!("a definition outside the opaque anchor must be refined")
        };
        assert_eq!(
            inventory.units[outside_facts_definition.0 as usize].full_range,
            outside_definition
        );
        assert_eq!(outside_rules.len(), 1);
        assert_eq!(
            inventory.units[outside_rules[0].0 as usize].full_range,
            outside_rule
        );
        assert!(inventory.units.iter().all(|unit| {
            unit.kind != WrittenUnitKind::MacroRule || !target.contains(unit.full_range)
        }));
        let opaque_definition = opaque_facts.definition();
        let mut incomplete = inventory.clone();
        incomplete
            .macro_rules
            .retain(|facts| facts.definition() != opaque_definition);
        assert_eq!(
            validate_macro_rule_facts(&incomplete.units, &incomplete.macro_rules),
            Err(SourceError::InvalidInventory)
        );

        merge_procedural_macro_atomic_groups(&mut inventory, &anchors).unwrap();

        let target_group = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == target)
            .unwrap()
            .atomic_group;
        assert!(inventory.units.iter().all(|unit| {
            !target.contains(unit.full_range) || unit.atomic_group == target_group
        }));
        assert_ne!(
            target_group,
            inventory
                .units
                .iter()
                .find(|unit| unit.full_range == outside_definition)
                .unwrap()
                .atomic_group
        );
    }

    #[test]
    fn procedural_derive_merges_future_nested_units_with_its_target() {
        let source = Arc::<str>::from(
            "#[derive(Generated)]\nstruct Subject { field: u8 }\nstruct Sibling;\n",
        );
        let target = marker(
            &source,
            "#[derive(Generated)]\nstruct Subject { field: u8 }",
        );
        let target_without_attribute = marker(&source, "struct Subject { field: u8 }");
        let derive = marker(&source, "#[derive(Generated)]");
        let field = marker(&source, "field: u8");
        let sibling = marker(&source, "struct Sibling;");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::Item, target, Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, derive, Some(1), 1),
            unit(3, WrittenUnitKind::NestedItem, field, Some(1), 2),
            unit(4, WrittenUnitKind::Item, sibling, Some(0), 3),
        ];
        let mut inventory = test_inventory(source, units, Vec::new());
        let invocation_range = marker(&inventory.original, "Generated");

        let anchors = resolve_procedural_macro_anchors(
            &inventory,
            vec![ObservedProceduralMacro::Target {
                invocation_range,
                node_range: target,
                target_range: target_without_attribute,
            }],
        )
        .unwrap();
        merge_procedural_macro_atomic_groups(&mut inventory, &anchors).unwrap();

        assert_eq!(
            inventory.units[1].atomic_group,
            inventory.units[3].atomic_group
        );
        assert_ne!(
            inventory.units[1].atomic_group,
            inventory.units[4].atomic_group
        );
    }

    #[test]
    fn procedural_macro_rejects_an_ambiguous_written_invocation() {
        let source = Arc::<str>::from("proc!();\n");
        let invocation = marker(&source, "proc!();");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::MacroInvocation, invocation, Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, invocation, Some(0), 2),
        ];
        let inventory = test_inventory(source, units, Vec::new());
        let invocation_range = marker(&inventory.original, "proc!()");

        assert_eq!(
            resolve_procedural_macro_anchors(
                &inventory,
                vec![ObservedProceduralMacro::Invocation {
                    invocation_range,
                    node_range: invocation,
                }],
            ),
            Err(SourceError::IncompleteProceduralMacroObservation)
        );
    }

    fn unit(
        id: u32,
        kind: WrittenUnitKind,
        full_range: ByteRange,
        parent: Option<u32>,
        atomic_group: u32,
    ) -> WrittenUnit {
        WrittenUnit {
            id: SourceUnitId(id),
            kind,
            full_range,
            parent: parent.map(SourceUnitId),
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(atomic_group),
            same_role_ordinal: 0,
        }
    }

    fn test_inventory(
        source: Arc<str>,
        units: Vec<WrittenUnit>,
        macro_rules: Vec<MacroRuleSourceFacts>,
    ) -> SourceInventory {
        let (normalized, offsets) = OriginalOffsetMap::from_source(&source).unwrap();
        let pieces = own_lexical_pieces(&source, &units).unwrap();
        SourceInventory {
            original: source,
            normalized: Arc::from(normalized),
            offsets,
            units,
            pieces,
            macro_rules,
            ownerless_attribute_invocations: Vec::new(),
        }
    }

    fn marker(source: &str, text: &str) -> ByteRange {
        let start = source.find(text).unwrap();
        ByteRange {
            start: start as u32,
            end: (start + text.len()) as u32,
        }
    }
}
