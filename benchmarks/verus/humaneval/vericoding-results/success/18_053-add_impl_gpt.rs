// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_safe_sub_max_minus_nonneg(y: i32)
    requires
        y >= 0,
    ensures
        0 <= i32::MAX - y,
        i32::MAX - y <= i32::MAX,
{ }

proof fn lemma_safe_sub_min_minus_neg(y: i32)
    requires
        y < 0,
    ensures
        i32::MIN <= i32::MIN - y,
        i32::MIN - y <= 0,
{ }

proof fn lemma_add_safe_when_nonneg_and_le_max_minus(x: i32, y: i32)
    requires
        y >= 0,
        x <= i32::MAX - y,
    ensures
        i32::MIN <= x + y,
        x + y <= i32::MAX,
{ }

proof fn lemma_add_safe_when_neg_and_ge_min_minus(x: i32, y: i32)
    requires
        y < 0,
        x >= i32::MIN - y,
    ensures
        i32::MIN <= x + y,
        x + y <= i32::MAX,
{ }
// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)

    ensures
        res.is_some() ==> res.unwrap() == x + y,
// </vc-spec>
// <vc-code>
{
    if y >= 0 {
        proof { lemma_safe_sub_max_minus_nonneg(y); }
        if x <= i32::MAX - y {
            proof { lemma_add_safe_when_nonneg_and_le_max_minus(x, y); }
            let z = x + y;
            Some(z)
        } else {
            None
        }
    } else {
        proof { lemma_safe_sub_min_minus_neg(y); }
        if x >= i32::MIN - y {
            proof { lemma_add_safe_when_neg_and_ge_min_minus(x, y); }
            let z = x + y;
            Some(z)
        } else {
            None
        }
    }
}
// </vc-code>

}
fn main() {}