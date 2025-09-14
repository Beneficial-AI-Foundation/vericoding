// <vc-preamble>
function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sum comprehension syntax */
lemma SumEquivalence(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
  ensures sumNegativesTo(a, n) == sum i | 0 <= i < n && a[i] < 0 :: a[i]
  decreases n
{
  if n > 0 {
    SumEquivalence(a, n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed sum comprehension syntax in invariant */
  var i := 0;
  result := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sum j | 0 <= j < i && a[j] < 0 :: a[j]
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    i := i + 1;
  }
  SumEquivalence(a, a.Length);
}
// </vc-code>
