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
function InsertSorted(s: seq<int>, v: int): seq<int>
  requires IsSorted(s) && NoDuplicates(s)
  ensures IsSorted(InsertSorted(s, v))
  ensures NoDuplicates(InsertSorted(s, v))
  ensures set(InsertSorted(s, v)) == set(s) + {v}
  decreases |s|
{
  if |s| == 0 then
    [v]
  else if s[0] == v then
    s
  else if s[0] < v then
    [s[0]] + InsertSorted(s[1..], v)
  else
    [v] + s
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
  var d := 1;
  result := [];
  // loop over potential divisors 1..n
  while d <= n
    invariant 1 <= d <= n + 1
    invariant IsSorted(result)
    invariant NoDuplicates(result)
    invariant set(result) == { f(n, dd) | dd :: 1 <= dd < d && IsDivisor(dd, n) }
  {
    if n % d == 0 {
      // preconditions for InsertSorted are maintained by invariants
      result := InsertSorted(result, f(n, d));
    }
    d := d + 1;
  }
  // At this point d == n+1 and invariant gives that result contains f(n,1) (since 1 divides n)
  assert |result| > 0;
}
// </vc-code>

