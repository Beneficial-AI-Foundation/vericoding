// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed termination and division by zero errors */
function MaxSum(arr: array<int>, start: int, end: int): int
    requires 0 <= start <= end <= arr.Length
    reads arr
    decreases end - start
{
    if start == end then 0
    else arr[start] + MaxSum(arr, start + 1, end)
}

function IsValidSubarray(start: int, end: int, k: int): bool
    requires k > 0
{
    (end - start) % k == 0
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
{
    /* code modified by LLM (iteration 2): simplified implementation without helper function calls */
    result := 0;
    var maxSum := 0;
    
    var i := 0;
    while i < arr.Length
    {
        var j := i + k;
        while j <= arr.Length
        {
            var currentSum := 0;
            var idx := i;
            while idx < j
            {
                currentSum := currentSum + arr[idx];
                idx := idx + 1;
            }
            if currentSum >= maxSum {
                maxSum := currentSum;
            }
            j := j + k;
        }
        i := i + 1;
    }
    
    result := maxSum;
}
// </vc-code>
