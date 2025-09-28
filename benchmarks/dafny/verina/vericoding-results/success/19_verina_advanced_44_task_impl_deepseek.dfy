// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): corrected sum function to handle base case and ensure proper termination */
function sum(arr: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= arr.Length
  reads arr
  decreases end - start
{
  if start == end then
    0
  else
    arr[start] + sum(arr, start + 1, end)
}

function max(a: int, b: int): int
  ensures a >= b ==> max(a, b) == a
  ensures b >= a ==> max(a, b) == b
{
  if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed syntax error in if condition */
  result := 0;
  var n := arr.Length;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var j := i;
    while j < n
      invariant i <= j <= n
    {
      if (j - i + 1) % k == 0 {
        var currentSum := sum(arr, i, j + 1);
        result := max(result, currentSum);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
