// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result ==> (forall k :: 0 <= k < i ==> n > a[k])
  {
    if n <= a[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
