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

// <vc-helpers>
proof fn lemma_verify_neg_step(a: &[int], idx: int)
    requires 0 <= idx < a.len()
    ensures verify_neg(a, idx+1) == verify_neg(a, idx) + (if a[idx] < 0 then 1 else 0)
{
    assert(verify_neg(a, idx+1) == verify_neg(a, idx) + (if a[idx] < 0 then 1 else 0));
}
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < n
        invariant 0 <= i <= n
        invariant cnt == verify_neg(a, i as int)
    {
        lemma_verify_neg_step(a, i as int);
        if a[i] < 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}
// </vc-code>

fn main() {
}

}