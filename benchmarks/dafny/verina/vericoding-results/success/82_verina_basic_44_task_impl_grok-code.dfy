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
  /* code modified by LLM (iteration 2): fixed loop invariants and changed loop to step by 1 instead of 2 to properly check all odd indices from 0 */
  var i := 0;
  result := true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> (forall j :: 0 <= j < i && j % 2 == 1 ==> IsOdd(a[j]))
  {
    if i % 2 == 1 {
      if !IsOdd(a[i]) {
        result := false;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
