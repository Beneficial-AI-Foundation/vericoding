This task involves finding the maximum possible "beauty" of an array after performing at most one operation. The beauty is defined as the maximum sum of any consecutive subarray (with empty subarrays having sum 0). The operation allows choosing any consecutive subarray and multiplying all its elements by a given integer x.

The implementation should use dynamic programming to efficiently compute the maximum beauty across all possible ways to apply the multiplier operation, including not applying it at all.

// ======= TASK =======
// Given an array of n integers, find the maximum possible "beauty" after performing at most one operation.
// The beauty is defined as the maximum sum of any consecutive subarray (empty subarray has sum 0).
// The operation allows you to choose any consecutive subarray and multiply all its elements by a given integer x.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(a: seq<int>, x: int)
{
    |a| >= 1 && 
    x >= -100 && x <= 100 &&
    forall i :: 0 <= i < |a| ==> a[i] >= -1000000000 && a[i] <= 1000000000
}

function MaxSubarraySum(a: seq<int>): int
{
    if |a| == 0 then 0
    else MaxSubarraySumHelper(a, 0, 0, 0)
}

function MaxSubarraySumHelper(a: seq<int>, i: int, currentSum: int, maxSoFar: int): int
    requires 0 <= i <= |a|
    decreases |a| - i
{
    if i == |a| then maxSoFar
    else
        var newCurrentSum := MaxInt(currentSum + a[i], 0);
        var newMaxSoFar := MaxInt(maxSoFar, newCurrentSum);
        MaxSubarraySumHelper(a, i + 1, newCurrentSum, newMaxSoFar)
}

function ApplyMultiplier(a: seq<int>, start: int, end: int, x: int): seq<int>
    requires 0 <= start <= end < |a|
    ensures |ApplyMultiplier(a, start, end, x)| == |a|
{
    a[..start] + MultiplySubarray(a[start..end+1], x) + a[end+1..]
}

function MultiplySubarray(subarray: seq<int>, x: int): seq<int>
    ensures |MultiplySubarray(subarray, x)| == |subarray|
{
    if |subarray| == 0 then []
    else [subarray[0] * x] + MultiplySubarray(subarray[1..], x)
}

function MaxBeautySpec(a: seq<int>, x: int): int
    requires ValidInput(a, x)
{
    MaxSubarraySum(a)
}

// ======= HELPERS =======
function MaxInt(a: int, b: int): int
{
    if a >= b then a else b
}

method ComputeMaxBeauty(a: seq<int>, x: int) returns (maxBeauty: int)
    requires ValidInput(a, x)
    ensures maxBeauty >= 0
{
    var n := |a|;
    var dp := new int[n+1, 4];

    dp[0, 0] := 0;
    dp[0, 1] := 0;
    dp[0, 2] := 0;
    dp[0, 3] := 0;

    for i := 1 to n+1
        invariant 1 <= i <= n+1
        invariant dp[i-1, 3] >= 0
        invariant dp[i-1, 0] >= 0
        invariant dp[i-1, 1] >= 0
        invariant dp[i-1, 2] >= 0
        invariant forall j :: 0 <= j < i ==> dp[j, 0] >= 0
        invariant forall j :: 0 <= j < i ==> dp[j, 1] >= 0
        invariant forall j :: 0 <= j < i ==> dp[j, 2] >= 0
        invariant forall j :: 0 <= j < i ==> dp[j, 3] >= 0
    {
        dp[i, 0] := MaxInt(dp[i-1, 0] + a[i-1], 0);
        dp[i, 1] := MaxInt(dp[i-1, 1] + a[i-1] * x, dp[i, 0]);
        dp[i, 2] := MaxInt(dp[i-1, 2] + a[i-1], dp[i, 1]);
        dp[i, 3] := MaxInt(dp[i-1, 3], dp[i, 2]);
    }

    maxBeauty := dp[n, 3];
}

// <vc-helpers>
// </vc-helpers>

// ======= MAIN METHOD =======
method FindMaxBeauty(a: seq<int>, x: int) returns (result: int)
    requires ValidInput(a, x)
    ensures result >= 0
{
    result := ComputeMaxBeauty(a, x);
}
