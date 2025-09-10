predicate ValidInput(test_cases: seq<seq<int>>)
{
    forall i :: 0 <= i < |test_cases| ==> |test_cases[i]| >= 1
}

function SumDifferences(arr: seq<int>, start: int): int
    requires 0 <= start <= |arr|
    decreases |arr| - start
{
    if start >= |arr| - 1 then 0
    else (if arr[start] > arr[start + 1] then arr[start] - arr[start + 1] else 0) + SumDifferences(arr, start + 1)
}

predicate CorrectResult(test_cases: seq<seq<int>>, results: seq<int>)
{
    |results| == |test_cases| &&
    forall i :: 0 <= i < |test_cases| ==> results[i] == SumDifferences(test_cases[i], 0) &&
    forall i :: 0 <= i < |results| ==> results[i] >= 0
}

// <vc-helpers>
method ComputeSum(arr: seq<int>) returns (res: int)
    requires |arr| >= 1
    ensures res == SumDifferences(arr, 0)
    ensures res >= 0
{
    var i := 0;
    res := 0;
    // res accumulates the contributions for indices [0..i-1]
    // Invariant: res + SumDifferences(arr, i) == SumDifferences(arr, 0)
    while i < |arr| - 1
        invariant 0 <= i <= |arr|
        invariant res + SumDifferences(arr, i) == SumDifferences(arr, 0)
        invariant res >= 0
        decreases |arr| - i
    {
        var delta := if arr[i] > arr[i+1] then arr[i] - arr[i+1] else 0;
        res := res + delta;
        i := i + 1;
    }
    // When loop exits, i >= |arr|-1, so SumDifferences(arr, i) == 0 and the invariant gives res == SumDifferences(arr,0)
}
// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<seq<int>>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures CorrectResult(test_cases, results)
// </vc-spec>
// <vc-code>
{
    var acc: seq<int> := [];
    var i := 0;
    while i < |test_cases|
        invariant 0 <= i <= |test_cases|
        invariant |acc| == i
        invariant forall k :: 0 <= k < |acc| ==> acc[k] == SumDifferences(test_cases[k], 0)
        invariant forall k :: 0 <= k < |acc| ==> acc[k] >= 0
        decreases |test_cases| - i
    {
        assert |test_cases[i]| >= 1;
        var v := ComputeSum(test_cases[i]);
        assert v >= 0;
        acc := acc + [v];
        i := i + 1;
    }
    results := acc;
}
// </vc-code>

