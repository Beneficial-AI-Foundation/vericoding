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
proof fn verify_neg_monotonic(a: &[int], i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures verify_neg(a, i) <= verify_neg(a, j)
    decreases j - i
{
    if i < j {
        verify_neg_monotonic(a, i, j - 1);
    }
}

proof fn verify_neg_step(a: &[int], i: int)
    requires 0 <= i < a.len()
    ensures verify_neg(a, i + 1) == verify_neg(a, i) + (if a[i] < 0 { 1nat } else { 0nat })
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            cnt == verify_neg(a, i as int)
    {
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        
        proof {
            verify_neg_step(a, i as int);
        }
        
        i = i + 1;
    }
    
    cnt
}
// </vc-code>

fn main() {
}

}