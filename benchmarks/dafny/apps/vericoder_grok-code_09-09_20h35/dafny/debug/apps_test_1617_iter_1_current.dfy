function f(n: int, x: int): int
  requires x > 0 && n >= x && n % x == 0
{
  var y := n / x;
  y + x * y * (y - 1) / 2
}

predicate IsDivisor(d: int, n: int)
{
  d > 0 && n % d == 0
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
function insert(v: int, s: seq<int>): seq<int>
 decreases |s|
{
  if |s| == 0 then [v] else if v < s[0] then [v] + s else [s[0]] + insert(v, s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires n >= 2
  ensures NoDuplicates(result)
  ensures IsSorted(result)
  ensures forall v :: v in result <==> exists d :: IsDivisor(d, n) && v == f(n, d)
  ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  var divisors : seq<int> := [];
  var i := 1;
  while i <= n {
    if IsDivisor(i, n) {
      divisors := divisors + [i];
    }
    i := i + 1;
  }
  var values : seq<int> := [];
  for k := 0 to |divisors|-1 {
    var d := divisors[k];
    var y := n / d;
    var v := y + d * y * (y - 1) / 2;
    values := values + [v];
  }
  var sorted : seq<int> := [];
  for k := 0 to |values|-1 {
    if !(values[k] in sorted) {
      sorted := insert(values[k], sorted);
    }
  }
  result := sorted;
}
// </vc-code>

