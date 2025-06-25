pub fn largest_sum(nums: &[i32], k: i32) -> (sum: i32)
    requires(nums.len() > 0)
    ensures(|sum: i32| max_sum_subarray(nums, sum, 0, nums.len()))
{
}

pub open spec fn max_sum_subarray(arr: &[i32], sum: i32, start: usize, stop: usize) -> bool
    recommends(arr.len() > 0)
    recommends(0 <= start <= stop <= arr.len())
{
    forall|u: usize, v: usize| start <= u < v <= stop ==> Sum_Array(arr, u, v) <= sum
}

pub open spec fn Sum_Array(arr: &[i32], start: usize, stop: usize) -> i32
    recommends(0 <= start <= stop <= arr.len())
    decreases(stop - start)
{
    if start >= stop {
        0
    } else {
        arr[stop - 1] + Sum_Array(arr, start, stop - 1)
    }
}