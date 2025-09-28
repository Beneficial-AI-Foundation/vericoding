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
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    let mut min_index: usize = from;
    let ghost mut min_val: i32 = a@[from as int];
    let ghost mut j: int = from as int + 1;
    while j < to as int
        invariant
            min_index >= from && min_index < to,
            j >= from as int + 1 && j <= to as int,
            forall|k: int| from as int <= k < j ==> #[trigger](a@[k] >= min_val),
        decreases to as int - j
    {
        if a@[j] < min_val {
            min_index = j as usize;
            min_val = a@[j];
        }
        j = j + 1;
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
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            i <= a.len() - 1,
            is_sorted(a@, 0, i as int),
            forall|j: int, k: int| 0 <= j < i && i <= k < a.len() ==> #[trigger](a@[j] <= a@[k]),
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases a.len() as int - i as int
    {
        let min_pos = find_min(a, i, a.len());
        a.swap(i, min_pos);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}