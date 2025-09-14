// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added preconditions and decreases to ensure safety and termination */
function SumSeq(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi+1 <= |s|
  decreases hi - lo + 1
{
  if lo > hi then 0 else s[lo] + SumSeq(s, lo+1, hi)
}
// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented scanning all subarrays and tracking max sum for lengths divisible by k */
  var n := arr.Length;
  if n == 0 {
    result := 0;
    return;
  }
  var start := 0;
  var found := false;
  var max := 0;
  while start < n
    decreases n - start
  {
    var end := start;
    var curr := 0;
    while end < n
      decreases n - end
    {
      curr := curr + arr[end];
      var len := end - start + 1;
      if len % k == 0 {
        if !found || curr > max {
          max := curr;
          found := true;
        }
      }
      end := end + 1;
    }
    start := start + 1;
  }
  if found {
    result := max;
  } else {
    result := 0;
  }
}
// </vc-code>
