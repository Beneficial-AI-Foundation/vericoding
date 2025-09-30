use vstd::prelude::*;

verus! {

// returns an index of the largest element of array 'a' in the range [0..n)

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn findMax(a: &[i32], n: usize) -> (r: usize)
    requires
        a.len() > 0,
        0 < n <= a.len(),
    ensures
        0 <= r < n <= a.len(),
        forall|k: usize| 0 <= k < n <= a.len() ==> a[r as int] >= a[k as int],
// </vc-spec>
// <vc-code>
{
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < n
        invariant
            0 <= max_idx < i <= n <= a.len(),
            forall|k: usize| 0 <= k < i ==> a[max_idx as int] >= a[k as int],
        decreases n - i,
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}

}