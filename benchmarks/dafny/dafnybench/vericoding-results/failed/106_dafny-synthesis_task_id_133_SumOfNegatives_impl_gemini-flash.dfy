function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

// <vc-helpers>
function sumNegativesTo'(a: array<int>, n: int): int
  requires 0 <= n <= a.Length
  reads a
  decreases n
{
  if n == 0 then 0 else if a[n - 1] < 0 then sumNegativesTo'(a, n - 1) + a[n - 1] else sumNegativesTo'(a, n - 1)
}
// </vc-helpers>

// <vc-spec>
method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var currentSum := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant currentSum == sumNegativesTo'(a, i)
        reads a
        decreases a.Length - i
    {
        if a[i] < 0 {
            currentSum := currentSum + a[i];
        }
        i := i + 1;
    }
    result := currentSum;
}
// </vc-code>

