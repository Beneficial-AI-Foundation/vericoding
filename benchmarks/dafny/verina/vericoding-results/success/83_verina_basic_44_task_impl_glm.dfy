// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fix loop invariant by allowing i up to a.Length+1 and adjust quantifier */
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length+1
    invariant forall j :: 1 <= j < i && j % 2 == 1 && j < a.Length ==> IsOdd(a[j])
    invariant i % 2 == 1
  {
    if !IsOdd(a[i]) {
      return false;
    }
    i := i + 2;
  }
  return true;
}
// </vc-code>
