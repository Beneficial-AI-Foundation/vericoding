use vstd::prelude::*;

verus! {

// ATOM 
spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: nat| i < a.len() - 1 ==> a[i as int] <= a[(i + 1) as int]
}

// SPEC 
pub fn bin_search(a: &[i32], k: i32) -> (b: bool)
    requires(is_sorted(a))
    ensures(b == exists|i: nat| i < a.len() && a[i as int] == k)
{
}

}