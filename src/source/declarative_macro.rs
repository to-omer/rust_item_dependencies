#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::TyCtxt;

#[cfg(rust_item_dependencies_patched)]
use crate::macro_output::ValidatedDeclarativeOutputs;

#[cfg(rust_item_dependencies_patched)]
use super::SourceError;
use super::{ByteRange, SourceUnitId};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroTemplateSourceFacts {
    pub unit: SourceUnitId,
    pub rule: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroCaptureInputSourceFacts {
    pub invocation: SourceUnitId,
    pub capture_range: ByteRange,
    pub deletion_range: ByteRange,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroCaptureSlotSourceFacts {
    pub unit: SourceUnitId,
    pub rule: SourceUnitId,
    pub matcher_capture_range: ByteRange,
    pub trigger_units: Vec<SourceUnitId>,
    pub inputs: Vec<MacroCaptureInputSourceFacts>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroRepetitionElementSourceFacts {
    pub unit: SourceUnitId,
    pub separator_after: Option<ByteRange>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroRepetitionSourceFacts {
    pub invocation: SourceUnitId,
    pub rule: SourceUnitId,
    pub matcher_range: ByteRange,
    pub parent: SourceUnitId,
    pub repetition_path: Vec<u32>,
    pub input_range: ByteRange,
    pub elements: Vec<MacroRepetitionElementSourceFacts>,
    pub minimum: u32,
    pub maximum: Option<u32>,
}

mod capture;
mod refinement;
mod repetition;
mod template;
#[cfg(test)]
mod tests;
mod validation;

pub(super) use validation::declarative_unit_kinds;
pub(crate) use validation::validate_declarative_macro_source_facts;

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn refine_declarative_macros_from_compiler(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &mut super::SourceInventory,
    outputs: &ValidatedDeclarativeOutputs,
) -> Result<(), SourceError> {
    refinement::validate_refinement_inventory(inventory)?;
    let observations =
        refinement::CompilerObservations::collect(compiler, tcx, inventory, outputs)?;
    let draft =
        refinement::RefinementDraft::build(compiler, tcx, inventory, outputs, &observations)?;
    draft.commit(inventory)
}
