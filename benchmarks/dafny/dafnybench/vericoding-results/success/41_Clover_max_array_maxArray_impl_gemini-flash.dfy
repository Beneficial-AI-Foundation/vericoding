

// <vc-helpers>
lemma MaxArrayProperty(a: array<int>, i: int, j: int, max_val: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i <= j
  requires forall k :: i <= k <= j ==> max_val >= a[k]
  ensures max_val >= a[i]
  ensures max_val >= a[j]
{}
// </vc-helpers>

// <vc-spec>
method maxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
// </vc-spec>
// <vc-code>
{
  var currentMax := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 < i <= a.Length
    invariant forall k :: 0 <= k < i ==> currentMax >= a[k]
    invariant exists k :: 0 <= k < i && currentMax == a[k]
  {
    if a[i] > currentMax {
      currentMax := a[i];
    }
    i := i + 1;
  }
  return currentMax;
}
// </vc-code>

