use vstd::prelude::*;

verus! {

// Sorts array 'a' using the insertion sort algorithm.
pub fn insertionSort(a: &mut Vec<i32>)
    requires(true)
    ensures(isSorted(a, 0, a.len() as nat))
    ensures(a@.to_multiset() == old(a)@.to_multiset())
{
}

// Checks if array 'a' is sorted.
pub open spec fn isSorted(a: &Vec<i32>, from: nat, to: nat) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: nat, j: nat| from <= i < j < to ==> a[i as int] <= a[j as int]
}

// Simple test case to check the postcondition
pub fn testInsertionSort()
    requires(true)
    ensures(true)
{
}

}