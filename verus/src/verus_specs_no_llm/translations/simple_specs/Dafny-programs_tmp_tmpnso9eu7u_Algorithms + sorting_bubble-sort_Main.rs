// Translated from Dafny
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

method Main() -> bool {
    var A := new int.index(10);
  A.index(0), A.index(1), A.index(2), A.index(3), A.index(4), A.index(5), A.index(6), A.index(7), A.index(8), A.index(9) := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  BubbleSort(A);
  print A.index(..)
}

}