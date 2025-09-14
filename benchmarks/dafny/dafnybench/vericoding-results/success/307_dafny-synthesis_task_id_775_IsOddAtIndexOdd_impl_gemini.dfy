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
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> (forall k :: 0 <= k < i ==> (IsOdd(k) ==> IsOdd(a[k])))
  {
    if IsOdd(i) && !IsOdd(a[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
