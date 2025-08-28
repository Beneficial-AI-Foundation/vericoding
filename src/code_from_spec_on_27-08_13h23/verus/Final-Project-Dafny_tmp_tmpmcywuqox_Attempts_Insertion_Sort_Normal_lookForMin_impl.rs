use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    sorted_a(a, a.len() as int)
}

spec fn sorted_a(a: &[int], i: int) -> bool {
    0 <= i <= a.len() && 
    forall|k: int| #![trigger a[k]] 0 < k < i ==> a[(k-1) as int] <= a[k]
}

// <vc-helpers>
proof fn lemma_min_value(a: &[int], i: usize, m: usize)
    requires 
        0 <= i < a.len(),
        i <= m < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
    ensures
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn look_for_min(a: &[int], i: usize) -> (m: usize)
    requires 
        0 <= i < a.len(),
    ensures
        i <= m < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn look_for_min(a: &[int], i: usize) -> (m: usize)
    requires 
        0 <= i < a.len(),
    ensures
        i <= m < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
{
    let mut min_idx = i;
    let mut j = i;
    
    while j < a.len()
        invariant
            i <= j <= a.len(),
            i <= min_idx < a.len(),
            forall|k: int| #![trigger a[k]] i <= k < j ==> a[k] >= a[min_idx as int],
    {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j = j + 1;
    }
    
    min_idx
}
// </vc-code>

fn main() {
}

}