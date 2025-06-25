use vstd::prelude::*;

verus! {

pub fn sortArray(arr: &mut Vec<i32>) -> (arr_sorted: Vec<i32>)
    requires(0 <= old(arr).len() < 10000)
    ensures(sorted(&arr_sorted, 0, arr_sorted.len() as int))
    ensures(multiset_equiv(old(arr)@, arr_sorted@))
{
}

pub open spec fn sorted(arr: &Vec<i32>, start: int, end: int) -> bool
    recommends(0 <= start <= end <= arr.len())
{
    forall|i: int, j: int| start <= i <= j < end ==> arr[i as usize] <= arr[j as usize]
}

}