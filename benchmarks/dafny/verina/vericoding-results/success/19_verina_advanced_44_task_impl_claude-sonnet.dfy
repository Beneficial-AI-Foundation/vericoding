// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to fix termination */ 
function SubarraySum(arr: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= arr.Length
  reads arr
  decreases end - start
{
  if start == end then 0
  else arr[start] + SubarraySum(arr, start + 1, end)
}

function MaxOfTwo(a: int, b: int): int
{
  if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop invariants for verification */
{
  if arr.Length == 0 {
    result := 0;
    return;
  }
  
  var maxSum := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
  {
    var j := i + k;
    while j <= arr.Length
      invariant i + k <= j <= arr.Length + k
    {
      var currentSum := SubarraySum(arr, i, j);
      maxSum := MaxOfTwo(maxSum, currentSum);
      j := j + k;
    }
    i := i + 1;
  }
  
  result := maxSum;
}
// </vc-code>
