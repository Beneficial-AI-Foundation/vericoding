// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(A: Vec<int>, 0, A.Length-1)
}


//ATOM

predicate sorted_between(A: Vec<int>, from: int, to: int)
  reads A
{
  forall i, j: : 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}


// SPEC

method BubbleSort(A:array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..])) -> bool {
    
}

}