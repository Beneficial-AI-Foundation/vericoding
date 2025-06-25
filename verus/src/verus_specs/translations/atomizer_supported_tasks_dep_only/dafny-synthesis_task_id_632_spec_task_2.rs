pub fn swap(arr: &mut [i32], i: usize, j: usize)
    requires
        arr.len() > 0,
        i < arr.len(),
        j < arr.len(),
    ensures
        arr[i as int] == old(arr)[j as int] && arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k],
        arr@.to_multiset() == old(arr)@.to_multiset(),
{
}