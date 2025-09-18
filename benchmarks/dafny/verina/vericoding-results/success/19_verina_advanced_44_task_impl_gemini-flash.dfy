// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): original implementation empty */
// No helpers needed, as the fix is in the main method's code block.

// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed array initialization */
{
    var n := arr.Length;
    if n == 0 {
        return 0;
    }

    var prefixSums := new int[n + 1];
    prefixSums[0] := 0;
    for i := 0 to n - 1 {
        prefixSums[i + 1] := prefixSums[i] + arr[i];
    }

    var maxLen := 0;
    for i := 0 to n - 1 {
        for j := i + 1 to n {
            var currentSum := prefixSums[j] - prefixSums[i];
            var currentLen := j - i;
            if currentSum % k == 0 && currentLen > maxLen {
                maxLen := currentLen;
            }
        }
    }
    result := maxLen;
}
// </vc-code>
