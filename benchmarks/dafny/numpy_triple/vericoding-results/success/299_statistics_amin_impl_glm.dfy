// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>
function minFloat(a: Float, b: Float): Float {
  if a == NaN || b == NaN then NaN
  else if a.val < b.val then a
  else b
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
  // Initialize result with first element
  result := a[0];
  
  // Iterate through the sequence to find minimum
  var i := 1;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant (exists j :: 0 <= j < i && a[j] == NaN) ==> result == NaN
    invariant (forall j :: 0 <= j < i ==> a[j] != NaN) ==> (exists j :: 0 <= j < i && a[j] == result)
    invariant (forall j :: 0 <= j < i ==> a[j] != NaN) ==> (forall j :: 0 <= j < i ==> a[j].Value? ==> result.Value? && result.val <= a[j].val)
  {
    result := minFloat(result, a[i]);
    i := i + 1;
  }
}
// </vc-code>
