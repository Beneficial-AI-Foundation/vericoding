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
function abs(x: int): int
{
    if x < 0 then -x else x
}

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

lemma MinTravelTimeLemma(t1: int, f1: int, t2: int, f2: int, a: int, b: int, h: int)
    requires ValidBuildingParams(1, h, a, b) && h >= 1
    requires 1 <= t1 <= 1 && 1 <= f1 <= h && 1 <= t2 <= 1 && 1 <= f2 <= h
    ensures MinTravelTime(t1, f1, t2, f2, a, b) >= 0
{
}

lemma MinTravelTimeSymmetry(t1: int, f1: int, t2: int, f2: int, a: int, b: int, h: int)
    requires ValidBuildingParams(1, h, a, b) && h >= 1
    requires 1 <= t1 <= 1 && 1 <= f1 <= h && 1 <= t2 <= 1 && 1 <= f2 <= h
    ensures MinTravelTime(t1, f1, t2, f2, a, b) == MinTravelTime(t2, f2, t1, f1, a, b)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, h: int, a: int, b: int, queries: seq<(int, int, int, int)>) returns (results: seq<int>)
    requires ValidBuildingParams(n, h, a, b)
    requires ValidQueries(queries, n, h)
    ensures CorrectResults(queries, results, a, b)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |results| == i
        invariant CorrectResults(queries[0..i], results, a, b)
    {
        var query := queries[i];
        var t1 := query.0;
        var f1 := query.1;
        var t2 := query.2;
        var f2 := query.3;
        
        var time := MinTravelTime(t1, f1, t2, f2, a, b);
        results := results + [time];
        i := i + 1;
    }
}
// </vc-code>

