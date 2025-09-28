// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed pow identifier */
  var prefix := new int[arr.Length + 1];
  prefix[0] := 0;
  for i := 1 to arr.Length + 1 {
    prefix[i] := prefix[i - 1] + arr[i - 1];
  }
  var maxSum := -1000000000;
  var found := false;
  for i := 0 to arr.Length + 1 {
    for j := 0 to arr.Length + 1 {
      if j > i && (j - i) % k == 0 {
        var currentSum := prefix[j] - prefix[i];
        if !found || currentSum > maxSum {
          found := true;
          maxSum := currentSum;
        }
      }
    }
  }
  if found {
    result := maxSum;
  } else {
    result := 0;
  }
}
// </vc-code>
