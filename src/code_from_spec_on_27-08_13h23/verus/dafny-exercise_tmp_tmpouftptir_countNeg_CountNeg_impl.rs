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
proof fn lemma_verify_neg(a: &[int], idx: int)
    requires 0 <= idx <= a.len() as int
    ensures verify_neg(a, idx) == verify_neg(a, idx)
    decreases idx
{
    if idx <= 0 {
    } else {
        lemma_verify_neg(a, idx - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == verify_neg(a, i as int)
    {
        if a[i] < 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        lemma_verify_neg(a, a.len() as int);
    }
    
    count
}
// </vc-code>

fn main() {
}

}