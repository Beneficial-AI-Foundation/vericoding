pub fn kth_element(arr: &[i32], k: i32) -> (result: i32)
    requires(1 <= k <= arr.len())
    ensures(result == arr[(k - 1) as usize])
{
}