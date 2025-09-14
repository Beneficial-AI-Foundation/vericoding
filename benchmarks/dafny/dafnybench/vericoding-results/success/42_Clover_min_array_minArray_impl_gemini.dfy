// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
// </vc-spec>
// <vc-code>
{
  r := a[0];
  var i : int := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> r <= a[k]
    invariant exists k :: 0 <= k < i && r == a[k]
  {
    if a[i] < r {
      r := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
