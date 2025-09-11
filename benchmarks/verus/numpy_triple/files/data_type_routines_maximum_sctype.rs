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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}