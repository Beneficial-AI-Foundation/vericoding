// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>
lemma Float_not_NaN_is_Value(a: Float)
  ensures a != NaN ==> a.Value?
{
  if a != NaN {
    match a {
      case Value(v) => {}
    }
  }
}
// </vc-helpers>

// <vc-spec>
method amin(a: seq<Float>) returns (result: Float)
  // Precondition: array must be non-empty since minimum is undefined for empty sets
  requires |a| > 0
  // Postcondition 1: if any element is NaN, result is NaN (NaN propagation)
  ensures (exists i :: 0 <= i < |a| && a[i] == NaN) ==> result == NaN
  // Postcondition 2: if no NaN present, result must be an actual element from the input array
  ensures (forall i :: 0 <= i < |a| ==> a[i] != NaN) ==> (exists i :: 0 <= i < |a| && a[i] == result)
  // Postcondition 3: if no NaN present, result must be less than or equal to all elements
  ensures (forall i :: 0 <= i < |a| ==> a[i] != NaN) ==> (forall i :: 0 <= i < |a| ==> a[i].Value? ==> result.Value? && result.val <= a[i].val)
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] != NaN
    decreases n - i
  {
    if a[i] == NaN {
      result := NaN;
      return;
    }
    i := i + 1;
  }
  // At this point, no element is NaN
  assert forall j :: 0 <= j < n ==> a[j] != NaN;
  var m := 0;
  i := 1;
  while i < n
    invariant 0 <= m < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] != NaN
    invariant forall j :: 0 <= j < i ==> a[m].Value? && a[j].Value? && a[m].val <= a[j].val
    decreases n - i
  {
    if a[i].Value? && a[m].Value? {
      if a[i].val < a[m].val {
        m := i;
      }
    }
    i := i + 1;
  }
  result := a[m];
}
// </vc-code>
