use vstd::prelude::*;

verus! {

// returns an index of the largest element of array 'a' in the range [0..n)

// <vc-helpers>
// empty
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
    let mut max_index = 0;
    for i in 1..n
        invariant
            0 <= max_index < i,
            i <= n,
            n <= a.len(),
            forall|k: int| 0 <= k < i ==> 
                0 <= max_index < a.len() && 0 <= k < a.len() && a[max_index as int] >= a[k as int],
    {
        if a[i] > a[max_index] {
            max_index = i;
        }
    }
    max_index
}
// </vc-code>

fn main() {}

}