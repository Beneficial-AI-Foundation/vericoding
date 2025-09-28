// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsMax(a: array<int>, k: int)
  reads a
  requires 0 <= k < a.Length
{
  forall i :: 0 <= i < a.Length ==> a[i] <= a[k]
}
// </vc-helpers>

// <vc-spec>
method Max(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= result
// </vc-spec>
// <vc-code>
{
    var currentMax := a[0];
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant exists k :: 0 <= k < i && currentMax == a[k]
      invariant forall k :: 0 <= k < i ==> a[k] <= currentMax
    {
      if a[i] > currentMax {
        currentMax := a[i];
      }
      i := i + 1;
    }
    result := currentMax;
}
// </vc-code>
