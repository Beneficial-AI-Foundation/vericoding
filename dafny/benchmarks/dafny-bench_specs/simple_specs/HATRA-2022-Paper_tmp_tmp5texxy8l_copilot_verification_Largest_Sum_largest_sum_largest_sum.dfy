//ATOM

// Predicate to confirm that sum is the maximum summation of element [start, stop) 
predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
  requires arr.Length > 0
  requires 0 <= start <= stop <= arr.Length
  reads arr
{
  forall u, v :: start <= u < v <= stop ==> Sum_Array(arr, u, v) <= sum
}


//ATOM


//Sums array elements between [start, stop)
function Sum_Array(arr: array<int>, start: int, stop: int): int
  requires 0 <= start <= stop <= arr.Length
  reads arr
{
  if start >= stop then 0
  else arr[stop-1] + Sum_Array(arr, start, stop-1)
}


// SPEC
// CoPilot function converted to dafny
method largest_sum(nums: array<int>, k: int) returns (sum: int)
  requires nums.Length > 0 
  ensures max_sum_subarray(nums, sum, 0, nums.Length)
{
}
