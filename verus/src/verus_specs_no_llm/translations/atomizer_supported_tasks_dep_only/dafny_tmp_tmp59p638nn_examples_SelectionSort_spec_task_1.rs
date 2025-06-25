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

// SPEC 

method SelectionnSort(a: Vec<int>) -> bool {
    
}

}