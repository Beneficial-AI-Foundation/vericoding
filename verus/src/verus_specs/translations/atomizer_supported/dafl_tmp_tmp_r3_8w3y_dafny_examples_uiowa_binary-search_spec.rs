use vstd::prelude::*;

verus! {

// ATOM 
spec fn isSorted(a: &[i32]) -> bool {
    forall|i: nat, j: nat| i < j < a.len() ==> a[i as int] <= a[j as int]
}

// SPEC
pub fn binSearch(a: &[i32], K: i32) -> (b: bool)
    requires(isSorted(a))
    ensures(b == exists|i: nat| i < a.len() && a[i as int] == K)
{
}

}