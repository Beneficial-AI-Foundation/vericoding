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
  var res: seq<int> := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |res| == i
    invariant forall j | 0 <= j < i ::
      var n := queries[j].0;
      var a := queries[j].1;
      var b := queries[j].2;
      res[j] == (if n % 2 == 0 then
                    if n * a <= (n / 2) * b then n * a else (n / 2) * b
                 else
                    if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a)
    decreases |queries| - i
  {
    var n := queries[i].0;
    var a := queries[i].1;
    var b := queries[i].2;
    var x := (if n % 2 == 0 then
                if n * a <= (n / 2) * b then n * a else (n / 2) * b
              else
                if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a);
    res := res + [x];
    i := i + 1;
  }
  results := res;
}
// </vc-code>

