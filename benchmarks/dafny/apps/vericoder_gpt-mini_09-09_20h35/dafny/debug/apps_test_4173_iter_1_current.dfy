predicate ValidQuery(query: (int, int, int))
{
    query.0 > 0 && query.1 > 0 && query.2 > 0
}

function MinCostForQuery(n: int, a: int, b: int): int
    requires n > 0 && a > 0 && b > 0
{
    if n % 2 == 0 then
        if n * a <= (n / 2) * b then n * a else (n / 2) * b
    else
        if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a
}

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(int, int, int)>) returns (results: seq<int>)
    requires forall i | 0 <= i < |queries| :: ValidQuery(queries[i])
    ensures |results| == |queries|
    ensures forall i | 0 <= i < |queries| :: 
        var n := queries[i].0;
        var a := queries[i].1;
        var b := queries[i].2;
        results[i] == (if n % 2 == 0 then
            if n * a <= (n / 2) * b then n * a else (n / 2) * b
        else
            if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a)
// </vc-spec>
// <vc-code>
{
  var r := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|;
    invariant |r| == i;
    invariant forall j | 0 <= j < i :: r[j] == MinCostForQuery(queries[j].0, queries[j].1, queries[j].2);
  {
    var q := queries[i];
    var n := q.0;
    var a := q.1;
    var b := q.2;
    var v := MinCostForQuery(n, a, b);
    r := r + [v];
    i := i + 1;
  }
  results := r;
}
// </vc-code>

