use vstd::prelude::*;

verus! {

// <vc-helpers>
fn get_min_idx(a: &Vec<i32>, start: int, end: int) -> (min_idx: int)
    requires
        0 <= start < end <= a.len(),
    ensures
        start <= min_idx < end,
        forall|k: int| start <= k < end ==> a[min_idx] <= a[k],
{
    let mut min_idx = start;
    let mut i = start + 1;
    while i < end
        invariant
            start <= min_idx < i <= end,
            forall|k: int| start <= k < i ==> a[min_idx] <= a[k],
    {
        if a[i as usize] < a[min_idx as usize] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut i: usize = 0;
    while i < n - 1
        invariant
            0 <= i && i < n,
            // Prefix a[0..i] is sorted
            forall|x: int, y: int| 0 <= x < y < i as int ==> a[x as usize] <= a[y as usize],
            // Elements in a[0..i] are less than or equal to elements in a[i..n]
            forall|x: int, y: int| 0 <= x < i as int && i as int <= y < n as int ==> a[x as usize] <= a[y as usize],
            // Multiset invariant
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let min_idx_ghost = get_min_idx(a, i as int, n as int);
        let min_idx: usize = min_idx_ghost as usize;
        let temp = a[i];
        a.set(i, a[min_idx]);
        a.set(min_idx, temp);
        i = i + 1;
    }

    // Post-condition proof
    proof {
        assert forall|j: int, k: int| 0 <= j < k < n implies a[j as usize] <= a[k as usize] by {
            if k < n - 1 {
                assert(a[j as usize] <= a[k as usize]);
            } else if j < n - 1 {
                 assert(a[j as usize] <= a[k as usize]);
            } else {
                 // j = n-1, k is out of bound. This branch is unreachable.
            }
        };
    }
}
// </vc-code>

fn main() {}

}