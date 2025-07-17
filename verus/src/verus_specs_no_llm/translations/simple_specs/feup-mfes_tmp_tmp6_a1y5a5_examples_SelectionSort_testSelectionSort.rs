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


//ATOM

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
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

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..])) -> bool {
    assume isSorted(a, 0, a.len());
  assume multiset(a.index(..)) ==> multiset(old(a.index(..)))
}

spec fn spec_findMin(a: Vec<real>, from: nat, to: nat) -> index: nat)
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

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..]))
{
  assume isSorted(a, 0, a.Length);
  assume multiset(a[..]) ==> multiset(old(a[..]));
}


// SPEC

method testSelectionSort(
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall |k: int| from <= k < to ==> a.index(k) >= a.index(index),
        isSorted(a, 0, a.len()),
        multiset(a.index(..)) == multiset(old(a.index(..)))
;

proof fn lemma_findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
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

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..]))
{
  assume isSorted(a, 0, a.Length);
  assume multiset(a[..]) ==> multiset(old(a[..]));
}


// SPEC

method testSelectionSort()
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall |k: int| from <= k < to ==> a.index(k) >= a.index(index),
        isSorted(a, 0, a.len()),
        multiset(a.index(..)) == multiset(old(a.index(..)))
{
    (0, 0, 0, 0, 0)
}

}