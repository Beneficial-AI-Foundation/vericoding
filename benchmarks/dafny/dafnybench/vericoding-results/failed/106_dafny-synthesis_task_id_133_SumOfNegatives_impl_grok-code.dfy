function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

// <vc-helpers>
function sumNegativesTo( a:array<int>, n:int ) : int
  requires 0 <= n && n <= a.Length
  decreases n
  reads a
  ensures n == 0 ==> result == 0
  ensures n > 0 && a[n-1] < 0 ==> result == sumNegativesTo(a, n-1) + a[n-1]
  ensures n > 0 && a[n-1] >= 0 ==> result == sumNegativesTo(a, n-1)
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}
// </vc-helpers>

// <vc-spec>
method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumNegativesTo(a, i)
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

