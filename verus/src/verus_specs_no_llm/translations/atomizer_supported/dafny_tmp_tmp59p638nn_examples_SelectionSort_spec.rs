// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Preserved(a: Vec<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

// ATOM 


ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a, 0, a.Length) && Preserved(a, 0, a.Length)
}


twostate predicate Sorted(a: Vec<int>, 0, a.Length) && Preserved(a, 0, a.Length)
}

// SPEC 

method SelectionnSort(a: Vec<int>) -> bool {
    
}

}