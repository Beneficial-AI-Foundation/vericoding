// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxDafnyLsp(a: array<int>) returns (x: int)
    requires a.Length > 0
    ensures 0 <= x < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[x]
// </vc-spec>
// <vc-code>
{
  x := 0;
  var i := 1;
  while i < a.Length
    invariant 0 <= x < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= a[x]
  {
    if a[i] > a[x] {
      x := i;
    }
    i := i + 1;
  }
}
// </vc-code>
