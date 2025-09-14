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
  /* code modified by LLM (iteration 3): fixed loop invariant to handle array bounds correctly */
  result := true;
  var i := 1;
  while i < a.Length
    invariant 0 <= i
    invariant i % 2 == 1
    invariant result <==> (forall j :: 0 <= j < a.Length && j < i && j % 2 == 1 ==> IsOdd(a[j]))
  {
    if !IsOdd(a[i]) {
      result := false;
      return;
    }
    i := i + 2;
  }
}
// </vc-code>
