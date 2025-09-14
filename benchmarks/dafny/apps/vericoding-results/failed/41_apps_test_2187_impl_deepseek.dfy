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
    if start < |arr| {
        if start < |arr| - 1 {
            SumDifferencesNonNegative(arr, start + 1);
        }
    }
}

lemma SumDifferencesTailZero(arr: seq<int>, n: int)
    requires n == |arr|
    ensures SumDifferences(arr, n) == 0
{
}

lemma SumDifferencesRecursive(arr: seq<int>, j: int, k: int)
    requires 0 <= j <= k <= |arr|
    ensures SumDifferences(arr, j) == (if j < |arr| - 1 && j < k then (if arr[j] > arr[j + 1] then arr[j] - arr[j + 1] else 0) else 0) + SumDifferences(arr, j + 1)
    decreases k - j
{
    if j < k {
        if j < |arr| {
            SumDifferencesRecursive(arr, j + 1, k);
        }
    }
}

lemma SumDifferencesBaseCase(arr: seq<int>, j: int)
    requires 0 <= j <= |arr|
    ensures j >= |arr| - 1 ==> SumDifferences(arr, j) == 0
{
    if j == |arr| {
    } else if j == |arr| - 1 {
    }
}

lemma SumDifferencesStep(arr: seq<int>, j: int)
    requires 0 <= j < |arr| - 1
    ensures SumDifferences(arr, j) == (if arr[j] > arr[j + 1] then arr[j] - arr[j + 1] else 0) + SumDifferences(arr, j + 1)
{
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
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == SumDifferences(test_cases[j], 0)
        invariant forall j :: 0 <= j < i ==> results[j] >= 0
    {
        var arr := test_cases[i];
        var sum := 0;
        var j := 0;
        
        assert |arr| >= 1 by {
            assert ValidInput(test_cases);
            assert 0 <= i < |test_cases|;
        }
        
        while j < |arr|
            invariant 0 <= j <= |arr|
            invariant sum == SumDifferences(arr, j)
            invariant sum >= 0
        {
            if j < |arr| - 1 && arr[j] > arr[j + 1] {
                sum := sum + (arr[j] - arr[j + 1]);
            }
            j := j + 1;
            
            if j <= |arr| {
                SumDifferencesNonNegative(arr, j);
            }
        }
        
        results := results + [sum];
        i := i + 1;
    }
}
// </vc-code>

