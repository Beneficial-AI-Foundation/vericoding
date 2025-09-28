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
spec fn verify_neg(a: &[int], idx: int) -> nat
    requires 0 <= idx <= a.len() as int
    decreases idx
{
    if idx <= 0 {
        0nat
    } else {
        verify_neg(a, idx - 1) + (if a@[idx - 1] < 0 { 1nat } else { 0nat })
    }
}
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
let mut cnt: usize = 0;
let mut i: usize = 0;
while i < a.len()
    invariant i <= a.len()
    invariant cnt == verify_neg(a, i as int) as usize
{
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