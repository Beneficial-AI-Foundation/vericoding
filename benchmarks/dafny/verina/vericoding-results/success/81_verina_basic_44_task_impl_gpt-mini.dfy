// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): function that checks odd elements at odd indices up to n */
function AllOddAtOddIndices(a: array<int>, n: int): bool
  reads a
  requires 0 <= n <= a.Length
{
  forall i :: 0 <= i < n && i % 2 == 1 ==> IsOdd(a[i])
}
// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented loop checking that every odd index contains an odd value */
  var i := 0;
  result := true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> (forall j :: 0 <= j < i && j % 2 == 1 ==> IsOdd(a[j]))
  {
    if i % 2 == 1 {
      result := result && IsOdd(a[i]);
    }
    i := i + 1;
  }
}
// </vc-code>
