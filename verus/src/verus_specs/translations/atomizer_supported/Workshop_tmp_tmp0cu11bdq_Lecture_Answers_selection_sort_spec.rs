use vstd::prelude::*;

verus! {

// ATOM 

spec fn sorted_prime(a: &Vec<i32>, i: usize) -> bool {
    forall|k: usize| 0 < k < i ==> a[k-1] <= a[k]
}

// SPEC 

pub fn selection_sort(a: &mut Vec<i32>)
    ensures
        sorted(a)
{
}

}