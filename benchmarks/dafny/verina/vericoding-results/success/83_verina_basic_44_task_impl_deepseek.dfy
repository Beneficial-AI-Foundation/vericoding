// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

predicate IsOddAtIndexOddHelper(a: array<int>, i: int)
  requires 0 <= i <= a.Length
  reads a
{
  if i == 0 then true else (i % 2 != 1 || IsOdd(a[i-1])) && IsOddAtIndexOddHelper(a, i-1)
}

// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error by adding reads clause */
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
