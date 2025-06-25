pub fn swap(arr: &mut [i32], i: usize, j: usize)
    requires(
        i < arr.len() && j < arr.len()
    )
    ensures(|arr_post: &[i32]|
        arr_post[i as int] == old(arr)[j as int] && 
        arr_post[j as int] == old(arr)[i as int]
    )
    ensures(|arr_post: &[i32]|
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> 
            arr_post[k] == old(arr)[k]
    )
{
}