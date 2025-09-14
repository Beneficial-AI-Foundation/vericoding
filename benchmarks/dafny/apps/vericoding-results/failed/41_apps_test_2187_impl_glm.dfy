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
lemma SumDifferencesNonNegative(arr: seq<int>, start: int)
    requires 0 <= start <= |arr|
    ensures SumDifferences(arr, start) >= 0
    decreases |arr| - start
{
    if start < |arr| - 1 {
        SumDifferencesNonNegative(arr, start+1);
        assert SumDifferences(arr, start) == 
            (if arr[start] > arr[start+1] then arr[start] - arr[start+1] else 0) + 
            SumDifferences(arr, start+1);
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
    results := [];
    var i := 0;
    while i < |test_cases|
        invariant 0 <= i <= |test_cases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            (results[j] == SumDifferences(test_cases[j], 0) && results[j] >= 0)
    {
        SumDifferencesNonNegative(test_cases[i], 0);
        results := results + [SumDifferences(test_cases[i], 0)];
        i := i + 1;
    }
    return results;
}
// </vc-code>

