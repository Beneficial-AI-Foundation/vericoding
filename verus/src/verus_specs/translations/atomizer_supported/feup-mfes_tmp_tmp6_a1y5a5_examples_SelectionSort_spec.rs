use vstd::prelude::*;

verus! {

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
spec fn isSorted(a: &[f64], from: nat, to: nat) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i as usize] <= a[j as usize]
}

// Sorts array 'a' using the selection sort algorithm.
pub fn selectionSort(a: &mut [f64])
    ensures isSorted(a, 0, a.len()),
    ensures a@.to_multiset() == old(a)@.to_multiset()
{
}

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
pub fn findMin(a: &[f64], from: nat, to: nat) -> (index: nat)
    requires 0 <= from < to <= a.len()
    ensures from <= index < to
    ensures forall|k: int| from <= k < to ==> a[k as usize] >= a[index as usize]
{
}

pub fn testSelectionSort()
{
}

pub fn testFindMin()
{
}

}