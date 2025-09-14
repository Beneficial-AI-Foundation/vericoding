function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

// <vc-helpers>
lemma sumToLemma(a: array<int>, n: int, m: int)
  requires a != null
  requires 0 <= n <= m <= a.Length
  ensures sumTo(a, m) == sumTo(a, n) + sumToHelper(a, n, m)
{
}

function sumToHelper(a: array<int>, from: int, to: int): int
  requires a != null
  requires 0 <= from <= to <= a.Length
  decreases to - from
  reads a
{
  if from == to then 0
  else a[from] + sumToHelper(a, from + 1, to)
}

lemma sumToEqualsHelper(a: array<int>, n: int)
  requires a != null
  requires 0 <= n <= a.Length
  ensures sumTo(a, n) == sumToHelper(a, 0, n)
{
  if n > 0 {
    sumToEqualsHelper(a, n-1);
  }
}
// </vc-helpers>

// <vc-spec>
method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumToHelper(a, 0, i)
  {
    result := result + a[i];
    i := i + 1;
  }
  sumToEqualsHelper(a, a.Length);
}
// </vc-code>

