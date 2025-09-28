// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int
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
  var n := arr.Length;
  result := 0;
  var i := 0;
  while i <= n
    decreases n - i
  {
    var currentSum := 0;
    var j := i;
    while j <= n
      decreases n - j
    {
      if (j - i) % k == 0 {
        result := max(result, currentSum);
      }
      if j < n {
        currentSum := currentSum + arr[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
