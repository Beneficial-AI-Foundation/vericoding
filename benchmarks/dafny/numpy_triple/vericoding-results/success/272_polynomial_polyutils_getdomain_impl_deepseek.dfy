// <vc-preamble>
// Method to compute the domain (smallest interval) containing all input points
// </vc-preamble>

// <vc-helpers>

  function min(a: real, b: real): real { if a < b then a else b }
  function max(a: real, b: real): real { if a > b then a else b }
  predicate inRange(x: real, low: real, high: real) { low <= x <= high }

// </vc-helpers>

// <vc-spec>
method getdomain(x: seq<real>) returns (result: seq<real>)
  // Input must be non-empty
  requires |x| >= 1
  // Output is exactly 2 elements: [min, max]
  ensures |result| == 2
  // The minimum is less than or equal to the maximum
  ensures result[0] <= result[1]
  // Every element in x is within the computed domain
  ensures forall i :: 0 <= i < |x| ==> result[0] <= x[i] <= result[1]
  // The domain bounds are actually achieved by elements in x
  ensures exists i :: 0 <= i < |x| && x[i] == result[0]
  ensures exists j :: 0 <= j < |x| && x[j] == result[1]
// </vc-spec>
// <vc-code>
{
  var minVal := x[0];
  var maxVal := x[0];
  var idx := 1;
  
  while idx < |x|
    invariant 0 <= idx <= |x|
    invariant minVal <= maxVal
    invariant forall k :: 0 <= k < idx ==> minVal <= x[k] <= maxVal
    invariant exists k :: 0 <= k < idx && x[k] == minVal
    invariant exists k :: 0 <= k < idx && x[k] == maxVal
  {
    if x[idx] < minVal {
      minVal := x[idx];
    }
    if x[idx] > maxVal {
      maxVal := x[idx];
    }
    idx := idx + 1;
  }
  
  result := [minVal, maxVal];
}
// </vc-code>
