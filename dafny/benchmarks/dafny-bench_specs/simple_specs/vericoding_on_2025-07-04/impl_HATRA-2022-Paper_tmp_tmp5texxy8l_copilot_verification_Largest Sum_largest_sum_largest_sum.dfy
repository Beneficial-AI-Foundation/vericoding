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


//IMPL 
// CoPilot function converted to dafny
method largest_sum(nums: array<int>, k: int) returns (sum: int)
  requires nums.Length > 0 
  ensures max_sum_subarray(nums, sum, 0, nums.Length)
{
  var max_so_far := nums[0];
  var max_ending_here := nums[0];
  
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    /* code modified by LLM (iteration 1): strengthened invariant to track maximum subarray sum found so far */
    invariant forall u, v :: 0 <= u < v <= i ==> Sum_Array(nums, u, v) <= max_so_far
    /* code modified by LLM (iteration 1): added invariant to track maximum subarray ending at position i-1 */
    invariant max_ending_here == Sum_Array(nums, MaxStartIndex(nums, i-1), i)
    /* code modified by LLM (iteration 1): added invariant to ensure max_ending_here contributes to max_so_far */
    invariant max_ending_here <= max_so_far
  {
    /* code modified by LLM (iteration 1): added assertion to help verification */
    assert max_ending_here + nums[i] == Sum_Array(nums, MaxStartIndex(nums, i-1), i+1) || 
           nums[i] == Sum_Array(nums, i, i+1);
    
    max_ending_here := if max_ending_here + nums[i] > nums[i] then max_ending_here + nums[i] else nums[i];
    max_so_far := if max_so_far > max_ending_here then max_so_far else max_ending_here;
    
    /* code modified by LLM (iteration 1): added assertion to maintain invariant */
    assert forall u, v :: 0 <= u < v <= i+1 ==> Sum_Array(nums, u, v) <= max_so_far;
    
    i := i + 1;
  }
  
  sum := max_so_far;
}

/* code modified by LLM (iteration 1): added helper function to find optimal start index */
function MaxStartIndex(nums: array<int>, pos: int): int
  requires nums.Length > 0
  requires 0 <= pos < nums.Length
  reads nums
  ensures 0 <= MaxStartIndex(nums, pos) <= pos
  ensures forall start :: 0 <= start <= pos ==> Sum_Array(nums, start, pos+1) <= Sum_Array(nums, MaxStartIndex(nums, pos), pos+1)
{
  if pos == 0 then 0
  else
    var prev_start := MaxStartIndex(nums, pos-1);
    if Sum_Array(nums, prev_start, pos) > 0 then prev_start else pos
}