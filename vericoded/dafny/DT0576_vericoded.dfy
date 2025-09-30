// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>

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
  var i := 0;
  var hasNaN := false;
  var minVal := a[0];
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant hasNaN ==> exists j :: 0 <= j < i && a[j] == NaN
    invariant !hasNaN ==> forall j :: 0 <= j < i ==> a[j] != NaN
    invariant !hasNaN && i > 0 ==> minVal.Value? && exists j :: 0 <= j < i && a[j] == minVal
    invariant !hasNaN && i > 0 ==> forall j :: 0 <= j < i ==> a[j].Value? ==> minVal.val <= a[j].val
    invariant hasNaN || i == 0 || minVal.Value?
  {
    if a[i] == NaN {
      hasNaN := true;
    } else if !hasNaN {
      if i == 0 || (minVal.Value? && a[i].val < minVal.val) {
        minVal := a[i];
      }
    }
    i := i + 1;
  }
  
  if hasNaN {
    result := NaN;
  } else {
    result := minVal;
  }
}
// </vc-code>
