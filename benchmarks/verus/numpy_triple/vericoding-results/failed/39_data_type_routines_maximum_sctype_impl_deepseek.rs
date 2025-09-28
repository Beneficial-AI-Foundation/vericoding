// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
enum NumericKind {

    Integer,

    UnsignedInteger,

    Float,

    Complex,

    String,

    Boolean,
}

#[derive(PartialEq, Eq, Structural)]
enum Precision {

    P8,

    P16,

    P32,

    P64,

    P128,

    P256,
}

#[derive(PartialEq, Eq, Structural)]
struct NumericType {

    kind: NumericKind,

    precision: Precision,
}

spec fn max_precision_for(kind: NumericKind) -> Precision {
    match kind {
        NumericKind::Integer => Precision::P64,
        NumericKind::UnsignedInteger => Precision::P64,
        NumericKind::Float => Precision::P128,
        NumericKind::Complex => Precision::P256,
        NumericKind::String => Precision::P64,
        NumericKind::Boolean => Precision::P8,
    }
}

spec fn precision_le(p1: Precision, p2: Precision) -> bool {
    match (p1, p2) {
        (Precision::P8, _) => true,
        (Precision::P16, Precision::P8) => false,
        (Precision::P16, _) => true,
        (Precision::P32, Precision::P8) => false,
        (Precision::P32, Precision::P16) => false,
        (Precision::P32, _) => true,
        (Precision::P64, Precision::P8) => false,
        (Precision::P64, Precision::P16) => false,
        (Precision::P64, Precision::P32) => false,
        (Precision::P64, _) => true,
        (Precision::P128, Precision::P256) => true,
        (Precision::P128, _) => false,
        (Precision::P256, _) => false,
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_precision_le_reflexive(p: Precision)
    ensures precision_le(p, p),
{
    match p {
        Precision::P8 => {},
        Precision::P16 => {},
        Precision::P32 => {},
        Precision::P64 => {},
        Precision::P128 => {},
        Precision::P256 => {},
    }
}

proof fn lemma_max_precision_is_max_for_kind(kind: NumericKind, p: Precision)
    ensures precision_le(p, max_precision_for(kind)),
{
    let max_p = max_precision_for(kind);
    match (kind, p) {
        (NumericKind::Integer, Precision::P8) => {},
        (NumericKind::Integer, Precision::P16) => {},
        (NumericKind::Integer, Precision::P32) => {},
        (NumericKind::Integer, Precision::P64) => {},
        (NumericKind::UnsignedInteger, Precision::P8) => {},
        (NumericKind::UnsignedInteger, Precision::P16) => {},
        (NumericKind::UnsignedInteger, Precision::P32) => {},
        (NumericKind::UnsignedInteger, Precision::P64) => {},
        (NumericKind::Float, Precision::P8) => {},
        (NumericKind::Float, Precision::P16) => {},
        (NumericKind::Float, Precision::P32) => {},
        (NumericKind::Float, Precision::P64) => {},
        (NumericKind::Float, Precision::P128) => {},
        (NumericKind::Complex, Precision::P8) => {},
        (NumericKind::Complex, Precision::P16) => {},
        (NumericKind::Complex, Precision::P32) => {},
        (NumericKind::Complex, Precision::P64) => {},
        (NumericKind::Complex, Precision::P128) => {},
        (NumericKind::Complex, Precision::P256) => {},
        (NumericKind::String, Precision::P8) => {},
        (NumericKind::String, Precision::P16) => {},
        (NumericKind::String, Precision::P32) => {},
        (NumericKind::String, Precision::P64) => {},
        (NumericKind::Boolean, Precision::P8) => {},
        _ => {},
    }
}
/* helper modified by LLM (iteration 5): Remove duplicate enum definition to fix compilation error */
// </vc-helpers>

// <vc-spec>
fn maximum_sctype(t: NumericType) -> (result: NumericType)
    ensures 
        result.kind == t.kind &&
        result.precision == max_precision_for(t.kind) &&
        precision_le(t.precision, result.precision)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Directly use t.kind without clone and verify against max_precision_for */
    NumericType {
        kind: t.kind,
        precision: match t.kind {
            NumericKind::Integer => Precision::P64,
            NumericKind::UnsignedInteger => Precision::P64,
            NumericKind::Float => Precision::P128,
            NumericKind::Complex => Precision::P256,
            NumericKind::String => Precision::P64,
            NumericKind::Boolean => Precision::P8,
        },
    }
}
// </vc-code>

}
fn main() {}