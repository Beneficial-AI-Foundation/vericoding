use vstd::prelude::*;

verus! {

spec fn sorted(a: &[i32], start: int, end: int) -> bool
    recommends
        0 <= start <= end <= a.len(),
{
    forall|j: int, k: int| start <= j < k < end ==> a[j] <= a[k]
}

pub fn insertion_sort(a: &mut Vec<i32>)
    requires
        a.len() > 1,
    ensures
        sorted(a, 0, a.len()),
{
}

pub fn main()
{
}

}