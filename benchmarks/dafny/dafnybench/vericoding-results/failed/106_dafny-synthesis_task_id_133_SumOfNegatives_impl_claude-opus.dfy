function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

// <vc-helpers>
lemma SumNegativesToInductive(a: array<int>, n: int)
    requires 0 <= n < a.Length
    ensures sumNegativesTo(a, n + 1) == sumNegativesTo(a, n) + (if a[n] < 0 then a[n] else 0)
{
    // This follows directly from the definition of sumNegativesTo
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
        SumNegativesToInductive(a, i);
        i := i + 1;
    }
}
// </vc-code>

