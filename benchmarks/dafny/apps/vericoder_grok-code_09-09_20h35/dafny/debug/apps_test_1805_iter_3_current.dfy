predicate ValidInput(queries: seq<int>) {
    forall i :: 0 <= i < |queries| ==> queries[i] >= 2
}

function MinAdditionalMatches(n: int): int
    requires n >= 2
{
    if n >= 4 then n % 2 else 4 - n
}

predicate ValidResult(queries: seq<int>, results: seq<int>)
    requires ValidInput(queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == MinAdditionalMatches(queries[i])
}

// <vc-helpers>
//
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidResult(queries, results)
// </vc-spec>
// <vc-code>
{
  var resultArr := new int[|queries|];
  for i := 0 to |queries| - 1
  {
    resultArr[i] := MinAdditionalMatches(queries[i]);
  }
  results := resultArr[..];
}
// </vc-code>

