use vstd::prelude::*;

verus! {

spec fn sorted_prime(a: &[i32], i: usize) -> bool
    recommends 0 <= i <= a.len()
{
    forall|k: usize| 0 < k < i ==> a[k-1] <= a[k]
}

pub fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(a)
{
}

}