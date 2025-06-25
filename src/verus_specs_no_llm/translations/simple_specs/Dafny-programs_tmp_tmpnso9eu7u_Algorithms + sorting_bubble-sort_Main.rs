// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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
    var A := new int.spec_index(10);
  A.spec_index(0), A.spec_index(1), A.spec_index(2), A.spec_index(3), A.spec_index(4), A.spec_index(5), A.spec_index(6), A.spec_index(7), A.spec_index(8), A.spec_index(9) := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  BubbleSort(A);
  print A.spec_index(..);
}

}