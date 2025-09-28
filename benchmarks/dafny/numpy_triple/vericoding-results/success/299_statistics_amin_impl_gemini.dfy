// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>
function minFloat(f1: Float, f2: Float): Float
{
  match f1 {
    case NaN => NaN
    case Value(v1) => match f2 {
      case NaN => NaN
      case Value(v2) => if v1 <= v2 then f1 else f2
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
  var current_min := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant (exists j :: 0 <= j < i && a[j] == NaN) ==> current_min == NaN
    invariant (forall j :: 0 <= j < i ==> a[j] != NaN) ==>
                (current_min.Value? &&
                 (exists k :: 0 <= k < i && a[k] == current_min) &&
                 (forall k :: 0 <= k < i ==> current_min.val <= a[k].val))
  {
    current_min := minFloat(current_min, a[i]);
    i := i + 1;
  }
  result := current_min;
}
// </vc-code>
