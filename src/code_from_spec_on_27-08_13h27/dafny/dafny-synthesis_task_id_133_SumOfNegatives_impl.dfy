function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var sum := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sum == sumNegativesTo(a, i)
  {
    if a[i] < 0 {
      sum := sum + a[i];
    }
    i := i + 1;
  }
  result := sum;
}
// </vc-code>
