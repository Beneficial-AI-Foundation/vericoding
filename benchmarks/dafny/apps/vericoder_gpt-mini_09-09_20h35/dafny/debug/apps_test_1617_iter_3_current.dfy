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
// (no helpers needed)
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
    invariant set(result) == set dd | 1 <= dd < d && IsDivisor(dd, n) :: f(n, dd)
  {
    if n % d == 0 {
      var v := f(n, d);
      if v in set(result) {
        // already present, do nothing
      } else {
        ghost var oldSet := set(result);
        if |result| == 0 {
          result := [v];
        } else if result[0] > v {
          result := [v] + result;
        } else {
          var i := 1;
          // find first index i such that result[i] >= v (or i == |result|)
          while i < |result| && result[i] < v
            invariant 1 <= i <= |result|
            invariant forall j :: 0 <= j < i ==> result[j] < v
            invariant IsSorted(result)
            invariant NoDuplicates(result)
          {
            i := i + 1;
          }
          // At this point either i == |result| or result[i] >= v.
          // Since v not in set(result), result[i] > v when i < |result|.
          result := result[..i] + [v] + result[i..];
        }
        assert set(result) == oldSet + {v};
      }
    }
    d := d + 1;
  }
  // At this point d == n+1 and invariant gives that result contains f(n,1) (since 1 divides n)
  assert |result| > 0;
}
// </vc-code>

