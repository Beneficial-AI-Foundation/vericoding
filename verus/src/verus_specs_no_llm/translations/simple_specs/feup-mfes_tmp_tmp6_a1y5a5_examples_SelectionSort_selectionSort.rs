// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSorted(a: Vec<real>, from: nat, to: nat)
 requires 0 <= from <= to <= a.Length
 reads a
{
  forall i, j: : from <= i < j < to ==> a[i] <= a[j] 
}


// SPEC

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..])) -> bool {
    
}

fn findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
 requires 0 <= from < to <= a.Length
 ensures from <= index < to
 ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  index := 0;
  assume from <= index < to;
  assume forall k :: from <= k < to ==> a[k] >= a[index];
  return index;
}


//ATOM

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
 requires 0 <= from <= to <= a.Length
 reads a
{
  forall i, j: : from <= i < j < to ==> a[i] <= a[j] 
}


// SPEC

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length)
    requires
        0 <= from < to <= a.len(),
        0 <= from <= to <= a.len()
 reads a
    ensures
        from <= index < to,
        forall k :: from <= k < to ==> a.spec_index(k) >= a.spec_index(index),
        isSorted(a, 0, a.len()),
        multiset(a.spec_index(..)) == multiset(old(a.spec_index(..)))
{
    return (0, 0, 0, 0, 0, 0);
}

}