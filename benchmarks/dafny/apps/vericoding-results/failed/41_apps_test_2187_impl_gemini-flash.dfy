// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<seq<int>>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures CorrectResult(test_cases, results)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation error: use a sequence constructor. */
{
    var r: seq<int> := new int (|test_cases|);
    for i := 0 to |test_cases| - 1
        invariant 0 <= i <= |test_cases|
        invariant |r| == |test_cases|
        invariant forall j :: 0 <= j < i ==> r[j] == SumDifferences(test_cases[j], 0)
    {
        r := r[i := SumDifferences(test_cases[i], 0)];
    }
    return r;
}
// </vc-code>
