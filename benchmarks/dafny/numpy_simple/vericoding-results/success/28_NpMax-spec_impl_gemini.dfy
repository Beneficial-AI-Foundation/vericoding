// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Max(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= result
// </vc-spec>
// <vc-code>
{
  var max := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant exists k :: 0 <= k < i && a[k] == max
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
  result := max;
}
// </vc-code>
