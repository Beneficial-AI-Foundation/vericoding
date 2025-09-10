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
    if start >= |arr| - 1 {
        // Base case: SumDifferences returns 0
    } else {
        // Recursive case
        var diff := if arr[start] > arr[start + 1] then arr[start] - arr[start + 1] else 0;
        assert diff >= 0;
        SumDifferencesNonNegative(arr, start + 1);
        assert SumDifferences(arr, start + 1) >= 0;
        assert SumDifferences(arr, start) == diff + SumDifferences(arr, start + 1);
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
    
    for i := 0 to |test_cases|
        invariant 0 <= i <= |test_cases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == SumDifferences(test_cases[j], 0)
        invariant forall j :: 0 <= j < |results| ==> results[j] >= 0
    {
        var sum := SumDifferences(test_cases[i], 0);
        SumDifferencesNonNegative(test_cases[i], 0);
        results := results + [sum];
    }
    
    assert |results| == |test_cases|;
    assert forall i :: 0 <= i < |test_cases| ==> results[i] == SumDifferences(test_cases[i], 0);
    assert forall i :: 0 <= i < |results| ==> results[i] >= 0;
}
// </vc-code>

