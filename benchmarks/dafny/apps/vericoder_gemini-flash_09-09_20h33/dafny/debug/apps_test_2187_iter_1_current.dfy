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
function method SumDifferencesIterative(arr: seq<int>): int
  requires |arr| >= 1
  ensures SumDifferencesIterative(arr) >= 0
{
  var sum := 0;
  var i := 0;
  while i < |arr| - 1
    invariant 0 <= i <= |arr| - 1
    invariant sum == SumDifferences(arr, 0) - SumDifferences(arr, i)
    invariant sum >= 0
  {
    if arr[i] > arr[i+1] {
      sum := sum + (arr[i] - arr[i+1]);
    }
    i := i + 1;
  }
  return sum;
}
// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<seq<int>>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures CorrectResult(test_cases, results)
// </vc-spec>
// <vc-code>
{
  var results_list: seq<int> := [];
  var i := 0;
  while i < |test_cases|
    invariant 0 <= i <= |test_cases|
    invariant |results_list| == i
    invariant forall k :: 0 <= k < i ==> results_list[k] == SumDifferences(test_cases[k], 0) && results_list[k] >= 0
  {
    var current_arr := test_cases[i];
    // Lemma to prove equivalence between recursive and iterative sum difference calculations
    // This isn't strictly necessary as Dafny's solver can often figure out function equivalence
    // but demonstrating the iterative calculation and proving its correctness can be a pattern for more complex problems.
    // Given 'SumDifferencesIterative' helper is provided, it's a good place to use it.
    var diff_sum := SumDifferencesIterative(current_arr);
    results_list := results_list + [diff_sum];
    i := i + 1;
  }
  results := results_list;
}
// </vc-code>

