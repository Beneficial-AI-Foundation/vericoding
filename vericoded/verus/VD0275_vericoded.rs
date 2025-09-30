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

// </vc-helpers>

// <vc-spec>
fn look_for_min(a: &[int], i: usize) -> (m: usize)
    requires 
        0 <= i < a.len(),
    ensures
        i <= m < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
// </vc-spec>
// <vc-code>
{
    let mut min_idx = i;
    let mut j = i + 1;
    
    while j < a.len()
        invariant
            i <= min_idx < a.len(),
            i + 1 <= j <= a.len(),
            forall|k: int| #![trigger a[k]] i <= k < j ==> a[k] >= a[min_idx as int],
        decreases a.len() - j,
    {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j += 1;
    }
    
    min_idx
}
// </vc-code>

fn main() {
}

}