use vstd::prelude::*;

verus! {

pub fn MoveZeroesToEnd(arr: &mut Vec<i32>)
    requires(arr.len() >= 2)
    ensures(arr.len() == old(arr).len())
    ensures(forall|i: int, j: int| 0 <= i < j < arr.len() && arr[i as usize] == 0 ==> arr[j as usize] == 0)
    ensures(arr@.to_multiset() == old(arr)@.to_multiset())
    ensures(forall|n: int, m: int| 0 <= n < m < arr.len() && old(arr)[n as usize] != 0 && old(arr)[m as usize] != 0 ==>
            exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k as usize] == old(arr)[n as usize] && arr[l as usize] == old(arr)[m as usize])
{
}

pub fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
    requires(arr.len() > 0)
    requires(i < arr.len() && j < arr.len())
    ensures(arr[i] == old(arr)[j] && arr[j] == old(arr)[i])
    ensures(forall|k: usize| k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k])
    ensures(arr@.to_multiset() == old(arr)@.to_multiset())
{
}

pub closed spec fn count(arr: Seq<i32>, value: i32) -> nat
    ensures(count(arr, value) <= arr.len())
{
    if arr.len() == 0 { 
        0 
    } else { 
        (if arr[0] == value { 1 } else { 0 }) + count(arr.subrange(1, arr.len() as int), value)
    }
}

}