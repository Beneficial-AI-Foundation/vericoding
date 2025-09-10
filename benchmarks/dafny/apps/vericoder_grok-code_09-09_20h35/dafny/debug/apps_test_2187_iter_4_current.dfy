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
predicate CorrectResult(test_cases: seq<seq<int>>, results: seq<int>)
{
    |results| == |test_cases| &&
    forall i :: 0 <= i < |test_cases| ==> (results[i] == SumDifferences(test_cases[i], 0) &&
    forall i :: 0 <= i < |results| ==> results[i] >= 0)
}

ghost method LemmaSumDifferencesNonNeg(arr: seq<int>, start: int)
    requires 0 <= start <= |arr|
    ensures SumDifferences(arr, start) >= 0
    decreases |arr| - start
{
    if start < |arr| - 1 {
        var temp := SumDifferences(arr, start + 1);
        LemmaSumDifferencesNonNeg(arr, start + 1);
        assert temp >= 0;
        var add := if arr[start] > arr[start + 1] then arr[start] - arr[start + 1] else 0;
        assert add >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<seq<int>>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures CorrectResult(test_cases, results)
// </vc-spec>
// <vc-code>
{
    var res := [];
    var i := 0;
    while i < |test_cases|
        invariant 0 <= i <= |test_cases|
        invariant |res| == i
        invariant forall k :: 0 <= k < i ==> res[k] == SumDifferences(test_cases[k], 0)
        invariant forall k :: 0 <= k < i ==> res[k] >= 0
    {
        var sum := SumDifferences(test_cases[i], 0);
        LemmaSumDifferencesNonNeg(test_cases[i], 0);
        assert sum >= 0;
        res := res + [sum];
        i := i + 1;
    }
    results := res;
}
// </vc-code>

