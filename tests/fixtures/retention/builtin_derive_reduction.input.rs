use std::cmp::Ordering;
use std::hash::Hash as UnusedHash;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

static CLONES: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug, Default, Hash)]
struct Basic(u8);

#[derive(UnusedHash)]
#[derive(Clone)]
struct SeparateAttributes(u8);

#[derive(Clone)]
#[derive(UnusedHash)]
#[derive(Debug)]
struct MiddleAttribute(u8);

#[derive(Clone)]
#[derive(UnusedHash)]
struct LastAttribute(u8);

#[derive(Clone, Default)]
enum UsedChoice {
    #[default] First,
    Second,
}

#[derive(Clone, Default)]
enum ChoiceWithoutDefaultUse {
    #[default] First,
}

#[derive(Copy)]
struct CountingField;

impl Clone for CountingField {
    fn clone(&self) -> Self {
        CLONES.fetch_add(1, AtomicOrdering::Relaxed);
        *self
    }
}

#[derive(Clone, Copy)]
struct CloneUsesCopy(CountingField);

#[derive(Copy)]
#[derive(Clone)]
struct CloneUsesPriorCopy(CountingField);

struct FieldOrder(u8);

impl PartialEq for FieldOrder {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for FieldOrder {}

impl PartialOrd for FieldOrder {
    fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
        Some(Ordering::Equal)
    }
}

impl Ord for FieldOrder {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[derive(PartialOrd, Ord)]
struct PartialOrdUsesOrd(FieldOrder);

impl PartialEq for PartialOrdUsesOrd {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for PartialOrdUsesOrd {}

#[derive(Ord)]
#[derive(PartialOrd)]
struct PartialOrdUsesPriorOrd(FieldOrder);

impl PartialEq for PartialOrdUsesPriorOrd {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for PartialOrdUsesPriorOrd {}

#[derive(PartialEq, Eq, Debug)]
struct StructuralInner(u8);

#[derive(PartialEq, Eq, Debug)]
struct StructuralOuter(StructuralInner);

const STRUCTURAL_PATTERN: StructuralOuter = StructuralOuter(StructuralInner(1));

fn main() {
    #[derive()]#[derive(Clone, Debug)]
    struct Local;

    println!("{:?}", Basic::default().clone());
    let _ = Local.clone();
    let _ = SeparateAttributes(1).clone();
    let _ = format!("{:?}", MiddleAttribute(2).clone());
    let _ = LastAttribute(3).clone();
    println!("{}", matches!(UsedChoice::default(), UsedChoice::First));
    let _ = ChoiceWithoutDefaultUse::First;

    let _ = CloneUsesCopy(CountingField).clone();
    let _ = CloneUsesPriorCopy(CountingField).clone();
    println!("{}", CLONES.load(AtomicOrdering::Relaxed));

    let ordering = PartialOrdUsesOrd(FieldOrder(1))
        .partial_cmp(&PartialOrdUsesOrd(FieldOrder(2)));
    println!("{ordering:?}");

    let prior_ordering = PartialOrdUsesPriorOrd(FieldOrder(1))
        .partial_cmp(&PartialOrdUsesPriorOrd(FieldOrder(2)));
    println!("{prior_ordering:?}");

    let structural = match StructuralOuter(StructuralInner(1)) {
        STRUCTURAL_PATTERN => "match",
        _ => "miss",
    };
    println!("{structural}");
}
