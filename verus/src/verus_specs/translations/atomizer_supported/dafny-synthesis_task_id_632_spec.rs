pub fn MoveZeroesToEnd(arr: &mut [i32])
    requires(arr.len() >= 2)
    ensures(arr.len() == old(arr).len())
    ensures(forall|i: usize, j: usize| 0 <= i < j < arr.len() && arr[i] == 0 ==> arr[j] == 0)
    ensures(arr@.to_multiset() == old(arr)@.to_multiset())
    ensures(forall|n: usize, m: usize| 0 <= n < m < arr.len() && old(arr)[n] != 0 && old(arr)[m] != 0 ==> 
            exists|k: usize, l: usize| 0 <= k < l < arr.len() && arr[k] == old(arr)[n] && arr[l] == old(arr)[m])
{
}

pub fn swap(arr: &mut [i32], i: usize, j: usize)
    requires(arr.len() > 0)
    requires(0 <= i < arr.len() && 0 <= j < arr.len())
    ensures(arr[i] == old(arr)[j] && arr[j] == old(arr)[i])
    ensures(forall|k: usize| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k])
    ensures(arr@.to_multiset() == old(arr)@.to_multiset())
{
}

pub fn count(arr: Seq<i32>, value: i32) -> (c: nat)
    ensures(c <= arr.len())
{
    if arr.len() == 0 { 0 } else { (if arr[0] == value { 1 } else { 0 }) + count(arr.skip(1), value) }
}