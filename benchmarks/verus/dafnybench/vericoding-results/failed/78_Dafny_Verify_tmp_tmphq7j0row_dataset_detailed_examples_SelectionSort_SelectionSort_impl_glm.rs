use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
fn swap(a: &mut Vec<i32>, i: usize, j: usize)
    requires
        0 <= (i as int) < a.len(),
        0 <= (j as int) < a.len(),
    ensures
        a@[i as int] == old(a@[j as int]),
        a@[j as int] == old(a@[i as int]),
        forall|k: int| 0 <= k < a.len() && k != (i as int) && k != (j as int) ==> a@[k] == old(a@[k]),
        a@.to_multiset() == old(a)@.to_multiset()
{
    let temp = a[i];
    a[i] = a[j];
    a[j] = temp;
}

fn find_min_index(a: &Vec<i32>, start: usize) -> (result: usize)
    requires
        0 <= (start as int) < a.len(),
    ensures
        (start as int) <= (result as int) < a.len(),
        forall|i: int| (start as int) <= i < a.len() ==> a[result] <= a[i]
{
    let mut min_index = start;
    let mut i = start + 1;
    while i < a.len()
        invariant
            (start as int) <= (min_index as int) < a.len(),
            (start as int) <= (i as int) <= a.len(),
            forall|k: int| (start as int) <= k < (i as int) ==> a[min_index] <= a[k]
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i += 1;
    }
    min_index
}
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
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= (i as int) <= n,
            forall|k1: int, k2: int| 0 <= k1 < k2 < (i as int) ==> a[k1] <= a[k2],
            a@.to_multiset() == old(a)@.to_multiset()
    {
        let min_index = find_min_index(a, i);
        if min_index != i {
            swap(a, i, min_index);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}