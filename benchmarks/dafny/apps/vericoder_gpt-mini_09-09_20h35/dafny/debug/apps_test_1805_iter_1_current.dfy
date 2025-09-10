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
// no helpers needed
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidResult(queries, results)
// </vc-spec>
// <vc-code>
{
  var a := new int[|queries|];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|;
    invariant a.Length == |queries|;
    invariant forall j :: 0 <= j < i ==> a[j] == MinAdditionalMatches(queries[j]);
  {
    a[i] := MinAdditionalMatches(queries[i]);
    i := i + 1;
  }
  results := a[..];
}
// </vc-code>

