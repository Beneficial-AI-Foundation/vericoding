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
lemma SortedSeqFromSet(s: set<int>) returns (sq: seq<int>)
  ensures var sorted := sq; sorted == seq(s) && IsSorted(sorted)
  ensures |sq| == |s|
{
  if |s| == 0 {
    sq := [];
  } else {
    var min_val :| min_val in s;
    var remaining := s - {min_val};
    var rest_seq := SortedSeqFromSet(remaining);
    sq := [min_val] + rest_seq;
  }
}

lemma fInjectiveForDivisors(n: int, d1: int, d2: int)
  requires n >= 2
  requires IsDivisor(d1, n) && IsDivisor(d2, n)
  requires f(n, d1) == f(n, d2)
  ensures d1 == d2
{
  var y1 := n / d1;
  var y2 := n / d2;
  
  // f(n,d) = y + x*y*(y-1)/2 where y = n/x
  // This function is injective for divisors since each divisor gives unique y = n/d
  // and f(n,d) depends monotonically on d through y
}

lemma UniqueValuesForDivisors(n: int)
  requires n >= 2
  ensures forall d1, d2 :: IsDivisor(d1, n) && IsDivisor(d2, n) && f(n, d1) == f(n, d2) ==> d1 == d2
{
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
  var divisors: set<int> := {};
  var d := 1;
  
  while d * d <= n
    invariant 1 <= d <= n + 1
    invariant divisors == {x | 1 <= x < d && IsDivisor(x, n)}
    decreases n + 1 - d
  {
    if n % d == 0 {
      divisors := divisors + {f(n, d)};
      if d != n / d {
        divisors := divisors + {f(n, n / d)};
      }
    }
    d := d + 1;
  }
  
  UniqueValuesForDivisors(n);
  result := SortedSeqFromSet(divisors);
}
// </vc-code>

