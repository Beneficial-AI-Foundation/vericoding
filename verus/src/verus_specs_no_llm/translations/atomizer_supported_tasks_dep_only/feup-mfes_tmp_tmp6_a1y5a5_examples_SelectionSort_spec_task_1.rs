// Translated from Dafny
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


// Sorts array 'a' using the selection sort algorithm.
// SPEC 

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..])) -> bool {
    
}

spec fn spec_selectionSort(a: Vec<real>, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{
}


// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
// SPEC 

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: Vec<real>, from: nat, to: nat) -> index: nat
    requires
        0 <= from < to <= a.len()
    ensures
        isSorted(a, 0, a.len()),
        multiset(a.index(..)) == multiset(old(a.index(..))),
        from <= index < to,
        forall |k: int| from <= k < to ==> a.index(k) >= a.index(index)
;

proof fn lemma_selectionSort(a: Vec<real>, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{
}


// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
// SPEC 

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
    requires
        0 <= from < to <= a.len()
    ensures
        isSorted(a, 0, a.len()),
        multiset(a.index(..)) == multiset(old(a.index(..))),
        from <= index < to,
        forall |k: int| from <= k < to ==> a.index(k) >= a.index(index)
{
    0
}

}