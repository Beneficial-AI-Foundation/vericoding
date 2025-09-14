function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

// <vc-helpers>
lemma sumNegativesToLemma(a: array<int>, n: int, i: int)
  requires a != null
  requires 0 <= i <= n <= a.Length
  ensures sumNegativesTo(a, n) == sumNegativesTo(a, i) + sumNegativesToFrom(a, i, n)
  decreases n - i
{
  if i < n {
    sumNegativesToLemma(a, n-1, i);
    if a[n-1] < 0 {
      assert sumNegativesTo(a, n) == sumNegativesTo(a, n-1) + a[n-1];
    } else {
      assert sumNegativesTo(a, n) == sumNegativesTo(a, n-1);
    }
    assert sumNegativesToFrom(a, i, n) == sumNegativesToFrom(a, i, n-1) + (a[n-1] < 0 ? a[n-1] : 0);
  }
}

function sumNegativesToFrom(a: array<int>, i: int, n: int): int
  requires a != null
  requires 0 <= i <= n <= a.Length
  decreases n - i
  reads a
{
  if i == n then 0
  else if a[i] < 0 then a[i] + sumNegativesToFrom(a, i+1, n)
  else sumNegativesToFrom(a, i+1, n)
}

lemma sumNegativesToFromZero(a: array<int>, n: int)
  requires a != null
  requires 0 <= n <= a.Length
  ensures sumNegativesToFrom(a, 0, n) == sumNegativesTo(a, n)
{
  if n > 0 {
    sumNegativesToFromZero(a, n-1);
    if a[n-1] < 0 {
      assert sumNegativesTo(a, n) == sumNegativesTo(a, n-1) + a[n-1];
      assert sumNegativesToFrom(a, 0, n) == sumNegativesToFrom(a, 0, n-1) + a[n-1];
    } else {
      assert sumNegativesTo(a, n) == sumNegativesTo(a, n-1);
      assert sumNegativesToFrom(a, 0, n) == sumNegativesToFrom(a, 0, n-1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumNegativesTo(a, i)
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    i := i + 1;
  }
  sumNegativesToFromZero(a, a.Length);
}
// </vc-code>

