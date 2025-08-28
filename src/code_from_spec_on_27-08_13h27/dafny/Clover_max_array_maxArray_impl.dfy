// <vc-helpers>
lemma MaxProperty(a: array<int>, m: int)
  requires a.Length >= 1
  requires forall k :: 0 <= k < a.Length ==> m >= a[k]
  requires exists k :: 0 <= k < a.Length && m == a[k]
  ensures true
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method maxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
// </vc-spec>
// </vc-spec>

// <vc-code>
method MaxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> m >= a[k]
    invariant exists k :: 0 <= k < i && m == a[k]
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
