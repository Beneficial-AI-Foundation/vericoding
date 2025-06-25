spec fn sum(arr: &[int], len: int) -> int
    recommends
        arr.len() > 0 && 0 <= len <= arr.len()
{
    if len == 0 { 0 } else { arr[len-1] + sum(arr, len-1) }
}

pub fn sum_array(arr: &[int]) -> (sum: int)
    requires
        arr.len() > 0
    ensures
        sum == sum(arr, arr.len() as int)
{
}