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
    /* code modified by LLM (iteration 5): removed explicit cast to int in comparison */
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            cnt == verify_neg(a, i as int),
        decreases a.len() - i
    {
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-code>

}
fn main() {}