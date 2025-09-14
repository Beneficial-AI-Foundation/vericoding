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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant (forall j :: 0 <= j < i && j % 2 == 1 ==> IsOdd(a[j]))
  {
    if i % 2 == 1 {
      if !IsOdd(a[i]) {
        return false;
      }
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
