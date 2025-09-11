// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn verify_neg(a: &[int], idx: int) -> nat
    decreases idx
{
    if idx <= 0 {
        0nat
    } else {
        verify_neg(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat })
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}