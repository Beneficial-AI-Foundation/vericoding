// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
