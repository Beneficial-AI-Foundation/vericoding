function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

// <vc-helpers>
lemma SumNegativesStep(a: array<int>, i: int)
  requires 0 <= i < a.Length
  reads a
  ensures sumNegativesTo(a, i+1) == sumNegativesTo(a, i) + (if a[i] < 0 then a[i] else 0)
{
  if a[i] < 0 {
    assert sumNegativesTo(a, i+1) == sumNegativesTo(a, i) + a[i]
  } else {
    assert sumNegativesTo(a, i+1) == sumNegativesTo(a, i)
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
    SumNegativesStep(a, i);
    assert result == sumNegativesTo(a, i+1);
    i := i + 1;
  }
}
// </vc-code>

