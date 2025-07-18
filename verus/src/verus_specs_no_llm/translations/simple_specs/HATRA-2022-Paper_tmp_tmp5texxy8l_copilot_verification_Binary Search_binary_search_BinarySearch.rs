// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn not_found(arr: Vec<int>, target: int)
reads arr
{
  (forall j :: 0 <= j < arr.Length ==> arr[j] != target)
}


//ATOM

// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length
reads arr
{
  if index == -1 then false
  else if arr[index] == target then true
  else false
}


//ATOM

// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{
  forall j, k: : 0 <= j < k < a.Length ==> a[j] <= a[k] 
}


//ATOM

// Predicate to that each element is unique
predicate distinct(arr: array<int>)
  reads arr
{
  forall i, j: : 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] != arr[j]
}


// SPEC
// Dafny verification of binary search alogirthm from binary_search.py
// Inspired by: https://ece.uwaterloo.ca/~agurfink/stqam/rise4fun-Dafny/#h211

method BinarySearch(arr: array<int>, target: int) returns (index: int)
  requires distinct(arr)
  requires sorted(arr)
  ensures -1 <= index < arr.Length
  ensures index == -1 ==> not_found(arr, target)
  ensures index != -1 ==> found(arr, target, index) -> bool {
    
}

spec fn spec_BinarySearch(arr: Vec<int>, target: int) -> index: int
    requires
        distinct(arr),
        sorted(arr)
    ensures
        -1 <= index < arr.len(),
        index == -1 ==> not_found(arr, target),
        index != -1 ==> found(arr, target, index)
;

proof fn lemma_BinarySearch(arr: Vec<int>, target: int) -> (index: int)
    requires
        distinct(arr),
        sorted(arr)
    ensures
        -1 <= index < arr.len(),
        index == -1 ==> not_found(arr, target),
        index != -1 ==> found(arr, target, index)
{
    0
}

}