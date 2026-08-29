//! Canonical, owned encoding of compiler terms.

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_middle::mir::interpret::AllocId;
use rustc_middle::ty::codec::TyEncoder;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_serialize::{Encodable, Encoder};
use rustc_span::{ByteSymbol, ExpnId, Span, SpanEncoder, Symbol, SyntaxContext};

use crate::definitions::CollectedDefinitions;
use crate::dependency_graph::DefinitionReferenceKey;
use crate::graph::{
    DefinitionKey, DefinitionOriginKey, ExternalDefinitionKey, GeneratedRole, InjectedRole,
};

const TERM_ENCODING_SCHEMA: u32 = 2;

/// A compiler term whose identity is independent of interned pointers and
/// compiler-session identifiers.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CanonicalCompilerTerm {
    pub schema_version: u32,
    pub bytes: Vec<u8>,
}

/// The semantic role of a top-level encoded value.
///
/// Keeping the role in the byte stream prevents structurally similar values
/// of different rustc types from sharing an identity accidentally.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CompilerTermKind {
    Type,
    Const,
    Region,
    GenericArgument,
    GenericArguments,
    Instance,
    TraitGoal,
    ProjectionGoal,
    Predicate,
    SolverSource,
    SolverTrace,
    AssociatedItemProof,
    VTable,
    Allocation,
    Synthetic,
}

impl CompilerTermKind {
    fn tag(self) -> u8 {
        match self {
            Self::Type => 0,
            Self::Const => 1,
            Self::Region => 2,
            Self::GenericArgument => 3,
            Self::GenericArguments => 4,
            Self::Instance => 5,
            Self::TraitGoal => 6,
            Self::ProjectionGoal => 7,
            Self::Predicate => 8,
            Self::SolverSource => 9,
            Self::SolverTrace => 10,
            Self::AssociatedItemProof => 11,
            Self::VTable => 12,
            Self::Allocation => 13,
            Self::Synthetic => 14,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CompilerTermError {
    MissingLocalDefinition,
    Span,
    Expansion,
    SyntaxContext,
    CrateNumber,
    DefinitionIndex,
    Allocation,
    IntegerWidth,
}

/// Encodes rustc values structurally while replacing every `DefId` with the
/// repository's source-derived local identity or the compiler's stable
/// external identity.
///
/// Unsupported session-local data records a delayed error. Encoding continues
/// only because rustc's `Encoder` trait is infallible; `canonicalize` never
/// returns bytes after such an observation.
pub(crate) struct TermHasher<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    definitions: &'a mut CollectedDefinitions,
    bytes: Vec<u8>,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    error: Option<CompilerTermError>,
}

impl<'a, 'tcx> TermHasher<'a, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, definitions: &'a mut CollectedDefinitions) -> Self {
        Self {
            tcx,
            definitions,
            bytes: Vec::new(),
            type_shorthands: FxHashMap::default(),
            predicate_shorthands: FxHashMap::default(),
            error: None,
        }
    }

    pub(crate) fn canonicalize<T>(
        &mut self,
        kind: CompilerTermKind,
        value: &T,
    ) -> Result<CanonicalCompilerTerm, CompilerTermError>
    where
        T: Encodable<Self>,
    {
        self.canonicalize_with(kind, |encoder| value.encode(encoder))
    }

    /// Encodes a compound value whose patched rustc container does not itself
    /// implement `Encodable`. The caller must emit every field and variant tag
    /// explicitly; this keeps unsupported compiler variants as compile errors.
    pub(crate) fn canonicalize_with(
        &mut self,
        kind: CompilerTermKind,
        encode: impl FnOnce(&mut Self),
    ) -> Result<CanonicalCompilerTerm, CompilerTermError> {
        self.bytes.clear();
        self.type_shorthands.clear();
        self.predicate_shorthands.clear();
        self.error = None;

        self.bytes.extend_from_slice(b"RIDTERM");
        self.emit_u8(kind.tag());
        encode(self);

        if let Some(error) = self.error {
            return Err(error);
        }
        Ok(CanonicalCompilerTerm {
            schema_version: TERM_ENCODING_SCHEMA,
            bytes: std::mem::take(&mut self.bytes),
        })
    }

    fn reject(&mut self, error: CompilerTermError) {
        self.error.get_or_insert(error);
        // Keep positions deterministic so shorthand bookkeeping can finish.
        self.bytes.push(0xff);
    }

    fn encode_definition_key(&mut self, key: &DefinitionKey) {
        self.emit_usize(key.0.len());
        for part in &key.0 {
            self.emit_u8(part.kind.rank());
            match &part.origin {
                DefinitionOriginKey::Written { anchor, unit_kind } => {
                    self.emit_u8(0);
                    self.emit_u32(anchor.start);
                    self.emit_u32(anchor.end);
                    self.emit_u8(unit_kind.rank());
                }
                DefinitionOriginKey::Expanded {
                    invocation_range,
                    generated_role,
                } => {
                    self.emit_u8(1);
                    self.emit_u32(invocation_range.start);
                    self.emit_u32(invocation_range.end);
                    self.encode_generated_role(*generated_role);
                }
                DefinitionOriginKey::CompilerGenerated { role } => {
                    self.emit_u8(2);
                    self.emit_u8(generated_role_tag(*role));
                }
                DefinitionOriginKey::Injected { role } => {
                    self.emit_u8(3);
                    self.emit_u8(injected_role_tag(*role));
                }
            }
            part.name.encode(self);
            self.emit_u32(part.same_role_ordinal);
        }
    }

    fn encode_external_definition_key(&mut self, key: &ExternalDefinitionKey) {
        self.emit_u64(key.crate_identity);
        self.emit_str(&key.crate_name);
        self.emit_raw_bytes(&key.def_path_hash);
    }

    fn encode_definition_reference(&mut self, reference: &DefinitionReferenceKey) {
        match reference {
            DefinitionReferenceKey::Local(key) => {
                self.emit_u8(0);
                self.encode_definition_key(key);
            }
            DefinitionReferenceKey::External(key) => {
                self.emit_u8(1);
                self.encode_external_definition_key(key);
            }
        }
    }

    fn encode_generated_role(&mut self, role: Option<GeneratedRole>) {
        match role {
            Some(role) => {
                self.emit_u8(1);
                self.emit_u8(generated_role_tag(role));
            }
            None => self.emit_u8(0),
        }
    }
}

fn generated_role_tag(role: GeneratedRole) -> u8 {
    match role {
        GeneratedRole::AnonymousAssociatedType => 0,
        GeneratedRole::AnonymousConst => 1,
        GeneratedRole::Coroutine => 2,
        GeneratedRole::CoroutineBody => 3,
        GeneratedRole::CoroutineClosure => 4,
        GeneratedRole::ElidedLifetime => 5,
        GeneratedRole::NestedStatic => 6,
        GeneratedRole::OpaqueLifetime => 7,
        GeneratedRole::OpaqueType => 8,
    }
}

fn injected_role_tag(role: InjectedRole) -> u8 {
    match role {
        InjectedRole::ExternCrate => 0,
        InjectedRole::PreludeImport => 1,
    }
}

impl Encoder for TermHasher<'_, '_> {
    fn emit_usize(&mut self, value: usize) {
        match u64::try_from(value) {
            Ok(value) => self.emit_u64(value),
            Err(_) => self.reject(CompilerTermError::IntegerWidth),
        }
    }

    fn emit_u128(&mut self, value: u128) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn emit_isize(&mut self, value: isize) {
        match i64::try_from(value) {
            Ok(value) => self.emit_i64(value),
            Err(_) => self.reject(CompilerTermError::IntegerWidth),
        }
    }

    fn emit_i128(&mut self, value: i128) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_i64(&mut self, value: i64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_i32(&mut self, value: i32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_i16(&mut self, value: i16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn emit_raw_bytes(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }
}

impl SpanEncoder for TermHasher<'_, '_> {
    fn encode_span(&mut self, _span: Span) {
        self.reject(CompilerTermError::Span);
    }

    fn encode_symbol(&mut self, symbol: Symbol) {
        self.emit_str(symbol.as_str());
    }

    fn encode_byte_symbol(&mut self, symbol: ByteSymbol) {
        self.emit_byte_str(symbol.as_byte_str());
    }

    fn encode_expn_id(&mut self, _expansion: ExpnId) {
        self.reject(CompilerTermError::Expansion);
    }

    fn encode_syntax_context(&mut self, _context: SyntaxContext) {
        self.reject(CompilerTermError::SyntaxContext);
    }

    fn encode_crate_num(&mut self, _crate_number: CrateNum) {
        self.reject(CompilerTermError::CrateNumber);
    }

    fn encode_def_index(&mut self, _definition_index: DefIndex) {
        self.reject(CompilerTermError::DefinitionIndex);
    }

    fn encode_def_id(&mut self, definition: DefId) {
        let reference = match self.definitions.target_key(self.tcx, definition) {
            Ok(reference) => reference,
            Err(_) => {
                self.reject(CompilerTermError::MissingLocalDefinition);
                return;
            }
        };
        self.encode_definition_reference(&reference);
    }
}

impl<'tcx> TyEncoder<'tcx> for TermHasher<'_, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = false;

    fn position(&self) -> usize {
        self.bytes.len()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, _allocation: &AllocId) {
        self.reject(CompilerTermError::Allocation);
    }
}
