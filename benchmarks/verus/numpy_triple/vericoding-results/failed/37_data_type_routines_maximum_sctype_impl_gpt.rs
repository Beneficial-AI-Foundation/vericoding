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
/* helper modified by LLM (iteration 5): helper lemmas to reason about precision_le ordering without bypasses */
proof fn lemma_p8_le_any(p2: Precision)
    ensures precision_le(Precision::P8, p2)
{ }

/* helper modified by LLM (iteration 5): P16 is <= any precision except P8 */
proof fn lemma_p16_le_not_p8(p2: Precision)
    requires p2 != Precision::P8
    ensures precision_le(Precision::P16, p2)
{ }

/* helper modified by LLM (iteration 5): P32 is <= any precision except P8 and P16 */
proof fn lemma_p32_le_not_p8_p16(p2: Precision)
    requires p2 != Precision::P8 && p2 != Precision::P16
    ensures precision_le(Precision::P32, p2)
{ }

/* helper modified by LLM (iteration 5): P64 is <= any precision >= P64 */
proof fn lemma_p64_le_not_smallers(p2: Precision)
    requires p2 != Precision::P8 && p2 != Precision::P16 && p2 != Precision::P32
    ensures precision_le(Precision::P64, p2)
{ }

/* helper modified by LLM (iteration 5): any non-P256 is <= P256 */
proof fn lemma_non_p256_le_p256(p: Precision)
    requires p != Precision::P256
    ensures precision_le(p, Precision::P256)
{ }
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
    /* code modified by LLM (iteration 5): removed bypass and used case analysis with helper lemmas */
    let kind = t.kind;
    let p = match kind {
        NumericKind::Integer => Precision::P64,
        NumericKind::UnsignedInteger => Precision::P64,
        NumericKind::Float => Precision::P128,
        NumericKind::Complex => Precision::P256,
        NumericKind::String => Precision::P64,
        NumericKind::Boolean => Precision::P8,
    };
    proof {
        assert(p == max_precision_for(kind));
        match t.precision {
            Precision::P8 => {
                lemma_p8_le_any(p);
            }
            Precision::P16 => {
                if p != Precision::P8 {
                    lemma_p16_le_not_p8(p);
                }
            }
            Precision::P32 => {
                if !(p == Precision::P8 || p == Precision::P16) {
                    lemma_p32_le_not_p8_p16(p);
                }
            }
            Precision::P64 => {
                if !(p == Precision::P8 || p == Precision::P16 || p == Precision::P32) {
                    lemma_p64_le_not_smallers(p);
                }
            }
            Precision::P128 => {
                if p == Precision::P256 {
                    lemma_non_p256_le_p256(Precision::P128);
                }
            }
            Precision::P256 => {
                // no derived fact here
            }
        }
    }
    let result = NumericType { kind, precision: p };
    result
}
// </vc-code>

}
fn main() {}