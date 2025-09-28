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
/* helper modified by LLM (iteration 2): name return variable to use 'result' in ensures */
fn max_precision_for_exec(kind: NumericKind) -> (result: Precision)
    ensures
        result == max_precision_for(kind),
{
    match kind {
        NumericKind::Integer => Precision::P64,
        NumericKind::UnsignedInteger => Precision::P64,
        NumericKind::Float => Precision::P128,
        NumericKind::Complex => Precision::P256,
        NumericKind::String => Precision::P64,
        NumericKind::Boolean => Precision::P8,
    }
}

/* helper modified by LLM (iteration 2): provide lemma stub with exhaustive case analysis */
proof fn lemma_precision_le_to_max_for_kind(p: Precision, k: NumericKind)
    ensures
        precision_le(p, max_precision_for(k)),
{
    match k {
        NumericKind::Integer => {
            match p {
                Precision::P8 => {}
                Precision::P16 => {}
                Precision::P32 => {}
                Precision::P64 => {}
                Precision::P128 => {}
                Precision::P256 => {}
            }
        }
        NumericKind::UnsignedInteger => {
            match p {
                Precision::P8 => {}
                Precision::P16 => {}
                Precision::P32 => {}
                Precision::P64 => {}
                Precision::P128 => {}
                Precision::P256 => {}
            }
        }
        NumericKind::Float => {
            match p {
                Precision::P8 => {}
                Precision::P16 => {}
                Precision::P32 => {}
                Precision::P64 => {}
                Precision::P128 => {}
                Precision::P256 => {}
            }
        }
        NumericKind::Complex => {
            match p {
                Precision::P8 => {}
                Precision::P16 => {}
                Precision::P32 => {}
                Precision::P64 => {}
                Precision::P128 => {}
                Precision::P256 => {}
            }
        }
        NumericKind::String => {
            match p {
                Precision::P8 => {}
                Precision::P16 => {}
                Precision::P32 => {}
                Precision::P64 => {}
                Precision::P128 => {}
                Precision::P256 => {}
            }
        }
        NumericKind::Boolean => {
            match p {
                Precision::P8 => {}
                Precision::P16 => {}
                Precision::P32 => {}
                Precision::P64 => {}
                Precision::P128 => {}
                Precision::P256 => {}
            }
        }
    }
}
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
    /* code modified by LLM (iteration 2): compute max precision for kind and construct result; invoke helper lemma */
    let kind = t.kind;
    let maxp = max_precision_for_exec(kind);
    proof { lemma_precision_le_to_max_for_kind(t.precision, kind); }
    NumericType { kind, precision: maxp }
}
// </vc-code>

}
fn main() {}