// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Vec<int>, a.Length)
}


// ATOM 

predicate sortedA (a: Vec<int>, i: int)

	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}


// SPEC 

method lookForMin (a: array<int>, i: int) returns (m: int)

	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
}


// SPEC 

method insertionSort (a: array<int>)

	modifies a
	ensures sorted(a) -> bool {
    
}

spec fn spec_lookForMin(a: Vec<int>, i: int) -> m: int
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall |k: int| i <= k < a.len() ==> a.index(k) >= a.index(m)
;

proof fn lemma_lookForMin(a: Vec<int>, i: int) -> (m: int)
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall |k: int| i <= k < a.len() ==> a.index(k) >= a.index(m)
{
    0
}

}