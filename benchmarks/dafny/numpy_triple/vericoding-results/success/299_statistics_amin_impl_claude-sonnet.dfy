// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>
predicate hasNaN(a: seq<Float>)
{
  exists i :: 0 <= i < |a| && a[i] == NaN
}

/* helper modified by LLM (iteration 3): added decreases clause to fix termination error */
function findMinValue(a: seq<Float>, start: int): Float
  requires 0 <= start < |a|
  requires forall i :: 0 <= i < |a| ==> a[i] != NaN
  ensures findMinValue(a, start) != NaN
  ensures exists i :: start <= i < |a| && a[i] == findMinValue(a, start)
  ensures forall i :: start <= i < |a| ==> a[i].Value? ==> findMinValue(a, start).Value? && findMinValue(a, start).val <= a[i].val
  decreases |a| - start
{
  if start == |a| - 1 then a[start]
  else
    var restMin := findMinValue(a, start + 1);
    if a[start].Value? && restMin.Value? && a[start].val <= restMin.val then a[start]
    else restMin
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
  /* code modified by LLM (iteration 3): basic implementation using helper functions */
  if hasNaN(a) {
    result := NaN;
  } else {
    result := findMinValue(a, 0);
  }
}
// </vc-code>
