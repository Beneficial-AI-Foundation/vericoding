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
lemma Lemma_f_equivalence(n: int, x: int)
  requires x > 0 && n >= x && n % x == 0
{
  calc {
    f(n, x);
    { reveal f(); }
    n / x + x * (n / x) * (n / x - 1) / 2;
    n / x + (n / x) * (n / x - 1) * x / 2;
    (n / x) * (1 + (n / x - 1) * x / 2);
    (n / x) * (2 / 2 + (n / x - 1) * x / 2);
    (n / x) * (2 + (n / x - 1) * x) / 2;
    (n / x) * (2 + n - x) / 2;
    (n / x) * (n + 2 - x) / 2;
  }
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
  var divisors := [1];
  var i := 2;
  while i * i <= n
    invariant 2 <= i <= n + 1
    invariant forall d :: d in divisors ==> IsDivisor(d, n)
    invariant forall d :: d in divisors ==> 1 <= d < i
    invariant NoDuplicates(divisors)
    invariant IsSorted(divisors)
  {
    if n % i == 0 {
      divisors := divisors + [i];
      if i * i != n {
        divisors := divisors + [n / i];
      }
    }
    i := i + 1;
  }
  if n > 1 {
    divisors := divisors + [n];
  }
  result := [];
  for d in divisors
    invariant IsSorted(result)
    invariant NoDuplicates(result)
    invariant forall v :: v in result <==> exists k :: k in divisors[..|divisors|] && k < d && v == f(n, k)
  {
    result := result + [f(n, d)];
  }
}
// </vc-code>

