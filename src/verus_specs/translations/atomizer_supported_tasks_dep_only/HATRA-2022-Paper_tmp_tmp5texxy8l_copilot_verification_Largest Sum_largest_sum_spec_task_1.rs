pub fn largest_sum(nums: &[int], k: int) -> (sum: int)
    requires(nums.len() > 0)
    ensures(|result: int| max_sum_subarray(nums, result, 0, nums.len()))
{
}

pub open spec fn max_sum_subarray(arr: &[int], sum: int, start: int, stop: int) -> bool
    recommends(
        arr.len() > 0,
        0 <= start <= stop <= arr.len()
    )
{
    forall|u: int, v: int| start <= u < v <= stop ==> Sum_Array(arr, u, v) <= sum
}

pub open spec fn Sum_Array(arr: &[int], start: int, stop: int) -> int
    recommends(0 <= start <= stop <= arr.len())
    decreases(stop - start)
{
    if start >= stop {
        0
    } else {
        arr[stop-1] + Sum_Array(arr, start, stop-1)
    }
}