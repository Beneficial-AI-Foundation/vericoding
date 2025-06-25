// ATOM 
spec fn Sum(arr: &[int], len: int) -> int
    recommends(arr.len() > 0 && 0 <= len <= arr.len())
{
    if len == 0 { 0 } else { arr[len-1] + Sum(arr, len-1) }
}

// SPEC 
pub fn SumArray(arr: &[int]) -> (sum: int)
    requires(arr.len() > 0)
    ensures(|result: int| result == Sum(arr, arr.len() as int))
{
}