use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
fn min_idx(a: &mut Vec<i32>, start: int, end: int) -> (ret: int)
    requires
        0 <= start < end <= a.len(),
    ensures
        start <= ret < end,
        forall|k: int| start <= k < end ==> a[ret] <= a[k],
{
    let mut min: i32 = a[start as usize];
    let mut min_i: int = start;

    let mut i: int = start + 1;
    while i < end
        invariant
            start < i <= end,
            start <= min_i < i,
            forall|k: int| start <= k < i ==> a[min_i] <= a[k],
            min == a[min_i],
            a.len() == old(a).len(),
            a@ === old(a)@, // The array itself remains unchanged during the search for min_idx
    {
        if a[i as usize] < min {
            min = a[i as usize];
            min_i = i;
        }
        i = i + 1;
    }
    return min_i;
}

proof fn swap_preserves_multiset<T>(a: &mut Vec<T>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        // Ensures the final array is sorted in ascending order
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        // Ensures that the final array has the same elements as the initial array
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len() as int;
    if n == 0 {
        return;
    }

    let old_a_multiset = a@.to_multiset();

    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            // Prefix a[0..i] is sorted
            forall|x: int, y: int| 0 <= x < y < i ==> a[x] <= a[y],
            // All elements in a[0..i] are less than or equal to elements in a[i..n]
            forall|x: int, y: int| 0 <= x < i && i <= y < n ==> a[x] <= a[y],
            // Multiset of elements remains unchanged
            a@.to_multiset() == old_a_multiset,
            a.len() == old(a).len(),
    {
        let min_val_idx: int = min_idx(a, i, n);
        
        if min_val_idx != i {
            a.swap(i as usize, min_val_idx as usize);
            proof {
                swap_preserves_multiset(a, i, min_val_idx);
            }
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}