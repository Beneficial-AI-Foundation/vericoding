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

spec fn sorted_between(A: Vec<int>, from: int, to: int)
    reads A
{
    forall i, j: : 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}


// ATOM 

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}


// SPEC 

method BubbleSort(A: Vec<int>) -> bool {
    
}

}