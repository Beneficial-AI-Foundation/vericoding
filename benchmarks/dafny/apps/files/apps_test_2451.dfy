// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, h: int, a: int, b: int, queries: seq<(int, int, int, int)>) returns (results: seq<int>)
    requires ValidBuildingParams(n, h, a, b)
    requires ValidQueries(queries, n, h)
    ensures CorrectResults(queries, results, a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
