// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): function Sum computes sum over [lo,hi) */
function Sum(arr: array<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= arr.Length
  reads arr
  decreases hi - lo
{
  if lo == hi then 0 else arr[lo] + Sum(arr, lo + 1, hi)
}

/* helper modified by LLM (iteration 4): lemma to relate Sum for hi+1 */
lemma SumAppend(arr: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi < arr.Length
  decreases hi - lo
  ensures Sum(arr, lo, hi + 1) == Sum(arr, lo, hi) + arr[hi]
{
  if lo == hi {
    // base case: Sum(arr, lo, lo+1) unfolds to arr[lo]
  } else {
    SumAppend(arr, lo + 1, hi);
  }
}

// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): scan all subarrays and update maximum sum for lengths divisible by k */
  var n := arr.Length;
  result := 0;
  if n >= k {
    var i := 0;
    while i <= n - k
      invariant 0 <= i <= n
      decreases n - i
    {
      var sum := 0;
      var m := i;
      while m < n
        invariant i <= m <= n
        invariant sum == Sum(arr, i, m)
        decreases n - m
      {
        sum := sum + arr[m];
        m := m + 1;
        SumAppend(arr, i, m - 1);
        if ( (m - i) % k == 0 ) {
          if sum > result {
            result := sum;
          }
        }
      }
      i := i + 1;
    }
  }
}

// </vc-code>
