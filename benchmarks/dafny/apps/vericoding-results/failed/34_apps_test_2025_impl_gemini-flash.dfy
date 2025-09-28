// <vc-preamble>
predicate IsComposite(x: int)
{
    x >= 4 && exists k :: 2 <= k < x && x % k == 0
}

predicate ValidInput(queries: seq<int>)
{
    forall i :: 0 <= i < |queries| ==> queries[i] >= 1
}

function MaxCompositeSummands(n: int): int
{
    if n % 4 == 0 then n / 4
    else if n % 4 == 1 && n / 4 >= 2 then n / 4 - 1
    else if n % 4 == 2 && n / 4 >= 1 then n / 4
    else if n % 4 == 3 && n / 4 >= 3 then n / 4 - 1
    else -1
}

predicate ValidResult(queries: seq<int>, results: seq<int>)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == MaxCompositeSummands(queries[i]) &&
    forall i :: 0 <= i < |queries| ==> results[i] >= -1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed. */
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidResult(queries, results)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): The previous implementation had no logical errors, but the `ValidResult` predicate in the preamble had an indentation warning that caused compilation to fail. This iteration ensures the solution for `solve` remains the same, as the issue was not with this code but with the predicate in the preamble. */
  results := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |results| == i
    invariant forall k :: 0 <= k < i ==> results[k] == MaxCompositeSummands(queries[k])
  {
    results := results + [MaxCompositeSummands(queries[i])];
    i := i + 1;
  }
}
// </vc-code>
