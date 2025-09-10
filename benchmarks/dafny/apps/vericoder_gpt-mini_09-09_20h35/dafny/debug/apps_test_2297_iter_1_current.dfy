predicate ValidQuery(query: (int, int))
{
    query.0 >= 1 && query.0 <= query.1
}

predicate ValidInput(queries: seq<(int, int)>)
{
    forall i :: 0 <= i < |queries| ==> ValidQuery(queries[i])
}

function ArrayElement(i: int): int
    requires i >= 1
{
    i * (if i % 2 == 1 then -1 else 1)
}

function RangeSum(l: int, r: int): int
    requires l >= 1
    decreases r - l + 1
{
    if l > r then 0 else ArrayElement(l) + RangeSum(l + 1, r)
}

function PrefixSum(k: int): int
{
    if k % 2 == 0 then k / 2 else -(k + 1) / 2
}

predicate CorrectResult(queries: seq<(int, int)>, results: seq<int>)
    requires ValidInput(queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == PrefixSum(queries[i].1) - PrefixSum(queries[i].0 - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures CorrectResult(queries, results)
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == PrefixSum(queries[j].1) - PrefixSum(queries[j].0 - 1)
    decreases |queries| - i
  {
    var q := queries[i];
    res := res + [PrefixSum(q.1) - PrefixSum(q.0 - 1)];
    i := i + 1;
  }
  results := res;
}
// </vc-code>

