

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method maxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var cur := a[0];
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> cur >= a[k]
    invariant exists k :: 0 <= k < i && cur == a[k]
  {
    if a[i] > cur {
      cur := a[i];
    }
    i := i + 1;
  }
  m := cur;
}
// </vc-code>

