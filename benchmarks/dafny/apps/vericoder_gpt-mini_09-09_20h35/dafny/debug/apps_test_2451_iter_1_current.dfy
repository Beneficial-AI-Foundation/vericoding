predicate ValidBuildingParams(n: int, h: int, a: int, b: int)
{
    n >= 1 && h >= 1 && 1 <= a <= b <= h
}

predicate ValidQuery(query: (int, int, int, int), n: int, h: int)
{
    1 <= query.0 <= n && 1 <= query.1 <= h &&
    1 <= query.2 <= n && 1 <= query.3 <= h
}

predicate ValidQueries(queries: seq<(int, int, int, int)>, n: int, h: int)
{
    forall i :: 0 <= i < |queries| ==> ValidQuery(queries[i], n, h)
}

function MinTravelTime(t1: int, f1: int, t2: int, f2: int, a: int, b: int): int
{
    if t1 == t2 then
        abs(f1 - f2)
    else if f1 >= a && f1 <= b then
        abs(t2 - t1) + abs(f2 - f1)
    else if f1 < a then
        abs(a - f1) + abs(t2 - t1) + abs(f2 - a)
    else
        abs(b - f1) + abs(t2 - t1) + abs(f2 - b)
}

predicate CorrectResults(queries: seq<(int, int, int, int)>, results: seq<int>, a: int, b: int)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==>
        var t1, f1, t2, f2 := queries[i].0, queries[i].1, queries[i].2, queries[i].3;
        results[i] == MinTravelTime(t1, f1, t2, f2, a, b)
}

// <vc-helpers>
// no helpers required
// </vc-helpers>

// <vc-spec>
method solve(n: int, h: int, a: int, b: int, queries: seq<(int, int, int, int)>) returns (results: seq<int>)
    requires ValidBuildingParams(n, h, a, b)
    requires ValidQueries(queries, n, h)
    ensures CorrectResults(queries, results, a, b)
// </vc-spec>
// <vc-code>
{
  var aarr := new int[|queries|];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|;
    invariant forall j :: 0 <= j < i ==>
      var t1 := queries[j].0; var f1 := queries[j].1; var t2 := queries[j].2; var f2 := queries[j].3;
      aarr[j] == MinTravelTime(t1, f1, t2, f2, a, b);
  {
    var q := queries[i];
    var t1 := q.0; var f1 := q.1; var t2 := q.2; var f2 := q.3;
    aarr[i] := MinTravelTime(t1, f1, t2, f2, a, b);
    i := i + 1;
  }
  results := aarr[..];
}
// </vc-code>

