// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Preserved(a: Vec<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

//ATOM_PLACEHOLDER_Ordered

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a, 0, a.Length) && Preserved(a, 0, a.Length)
}

//ATOM_PLACEHOLDER_SelectionnSort

// SPEC 

 method SelectionSort(a: Vec<int>) -> bool {
    
}

}