//! Stable doc-attribute tags attached to compiler definitions.

use std::collections::{BTreeMap, BTreeSet};

use rustc_ast::AttrStyle;
use rustc_ast::token::DocFragmentKind;
use rustc_ast::util::comments::beautify_doc_string;
use rustc_hir::attrs::{Attribute, AttributeKind};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use crate::definitions::CollectedDefinitions;
use crate::graph::{DefinitionId, DefinitionOrigin};
use crate::source::{ByteRange, SourceInventory, original_span_range};

const TAG_PREFIX: &str = "rust-item-dependencies:tag=";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TagError {
    InvalidTag(ByteRange),
    InvalidSource,
}

pub(crate) type DefinitionTags = BTreeMap<DefinitionId, BTreeSet<String>>;

pub(crate) fn collect_definition_tags(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
) -> Result<DefinitionTags, TagError> {
    let mut tags = BTreeMap::<DefinitionId, BTreeSet<String>>::new();
    for local in tcx.iter_local_def_id() {
        if !definitions.has_hir_definition(local) {
            continue;
        }
        let Some(definition_id) = definitions.definition_id(local) else {
            return Err(TagError::InvalidSource);
        };
        let hir_id = tcx.local_def_id_to_hir_id(local);
        for attribute in tcx.hir_attrs(hir_id) {
            let Attribute::Parsed(AttributeKind::DocComment {
                style: AttrStyle::Outer,
                kind,
                span,
                comment,
            }) = attribute
            else {
                continue;
            };
            let decoded = match kind {
                DocFragmentKind::Sugared(kind) => beautify_doc_string(*comment, *kind),
                DocFragmentKind::Raw(_) => *comment,
            };
            let Some(tag) = decoded.as_str().strip_prefix(TAG_PREFIX) else {
                continue;
            };
            if tag.is_empty() {
                let range = original_span_range(compiler, &source.offsets, span.source_callsite())
                    .ok()
                    .or_else(|| definition_range(definitions, definition_id))
                    .ok_or(TagError::InvalidSource)?;
                return Err(TagError::InvalidTag(range));
            }
            tags.entry(definition_id)
                .or_default()
                .insert(tag.to_owned());
        }
    }
    Ok(tags)
}

fn definition_range(
    definitions: &CollectedDefinitions,
    definition: DefinitionId,
) -> Option<ByteRange> {
    match definitions
        .graph
        .definitions
        .get(definition.0 as usize)?
        .origin
    {
        DefinitionOrigin::Written { anchor, .. } => Some(anchor),
        DefinitionOrigin::Expanded {
            invocation_range, ..
        } => Some(invocation_range),
        DefinitionOrigin::CompilerGenerated { .. } | DefinitionOrigin::Injected { .. } => None,
    }
}
