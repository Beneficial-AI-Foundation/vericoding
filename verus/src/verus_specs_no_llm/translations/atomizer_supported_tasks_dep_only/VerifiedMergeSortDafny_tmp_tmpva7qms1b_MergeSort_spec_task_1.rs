// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_slice(a: Vec<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j: : start <= i <= j < end ==> a[i] <= a[j]
}


// ATOM 

predicate sorted_seq(a: seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < a.len() ==> a.index(i) <= a.index(j)
}

}