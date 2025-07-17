// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Vec<int>, 0, a.Length)
}


//ATOM
predicate sorted_between (a: Vec<int>, from: nat, to: nat)
 reads a
 requires a != null
 requires from <= to
 requires to <= a.Length
{
 forall i, j: : from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}


// SPEC

method bubbleSort (a: array<int>)
 modifies a
 requires a != null
 requires a.Length > 0
 ensures sorted(a)
 ensures multiset(old(a[..])) == multiset(a[..]) -> bool {
    
}

}