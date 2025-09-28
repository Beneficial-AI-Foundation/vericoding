use vstd::prelude::*;

verus! {

/* 
* Formal verification of the selection sort algorithm with Verus.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
spec fn is_sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    assume(false);
    0
}

// <vc-helpers>
fn find_min_impl(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    let mut min_index = from;
    let mut i = from + 1;
    while i < to
        invariant 
            from <= min_index < i,
            forall|k: int| from as int <= k < i as int ==> a@[k] >= a@[min_index as int],
            i <= to
        decreases to - i
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures 
        is_sorted(a@, 0, a@.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    for i in 0..n
        invariant
            0 <= i <= n,
            is_sorted(a@, 0, i as int),
            forall|j: int, k: int| 0 <= j < i as int && i as int <= k < n as int ==> a@[j] <= a@[k],
            a@.to_multiset() == old(a)@.to_multiset()
    {
        let min_index = find_min_impl(a, i, n);
        if i != min_index {
            let temp = a[i];
            a[i] = a[min_index];
            a[min_index] = temp;
        }
    }
}
// </vc-code>

fn main() {}

}