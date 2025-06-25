pub fn replace(arr: &mut [i32], k: i32)
    requires true
    ensures forall|i: usize| 0 <= i < arr.len() ==> old(arr)[i] > k ==> arr[i] == -1
    ensures forall|i: usize| 0 <= i < arr.len() ==> old(arr)[i] <= k ==> arr[i] == old(arr)[i]
{
}