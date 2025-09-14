function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

// <vc-helpers>
lemma SumToExtend(a: array<int>, n: int)
  requires 0 <= n < a.Length
  ensures sumTo(a, n+1) == sumTo(a, n) + a[n]
{
  assert 0 <= n + 1 && n + 1 <= a.Length
  assert 0 <= n && n <= a.Length
  calc {
    sumTo(a, n + 1);
    == { assert n + 1 != 0; }
    sumTo(a, (n + 1) - 1) + a[(n + 1) - 1];
    == { assert (n + 1) - 1 == n; }
    sumTo(a, n) + a[n];
  }
}
// </vc-helpers>

// <vc-spec>
method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == sumTo(a, i)
    decreases a.Length - i
  {
    SumToExtend(a, i);
    s := s + a[i];
    i := i + 1;
  }
  result := s;
}
// </vc-code>

