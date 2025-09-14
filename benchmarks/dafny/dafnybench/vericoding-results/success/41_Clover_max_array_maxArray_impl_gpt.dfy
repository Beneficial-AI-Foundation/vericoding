

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
  var i := 0;
  m := a[0];
  i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> m >= a[k]
    invariant exists k :: 0 <= k < i && m == a[k]
    decreases a.Length - i
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

