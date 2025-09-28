// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
function OddIndicesOK(a: array<int>, n: int): bool
  requires 0 <= n <= a.Length
  reads a
{
  forall i :: 0 <= i < n && i % 2 == 1 ==> IsOdd(a[i])
}

function AllOddIndicesOdd(a: array<int>): bool
  reads a
{
  OddIndicesOK(a, a.Length)
}
// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> (forall j :: 0 <= j < i && j % 2 == 1 ==> IsOdd(a[j]))
  {
    var r := result;
    if i % 2 == 1 {
      if !IsOdd(a[i]) {
        r := false;
      }
    }
    i := i + 1;
    result := r;
  }
}
// </vc-code>
