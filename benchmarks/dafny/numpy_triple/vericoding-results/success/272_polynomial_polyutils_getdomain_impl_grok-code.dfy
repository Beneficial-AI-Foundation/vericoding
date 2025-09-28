// <vc-preamble>
// Method to compute the domain (smallest interval) containing all input points
// </vc-preamble>

// <vc-helpers>

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
  var min_val, max_val := x[0], x[0];
  var i := 1;
  while i < |x|
    invariant 1 <= i <= |x|
    invariant min_val <= max_val
    invariant forall j :: 0 <= j < i ==> min_val <= x[j] <= max_val
    invariant exists j :: 0 <= j < i && x[j] == min_val
    invariant exists k :: 0 <= k < i && x[k] == max_val
  {
    min_val := if x[i] < min_val then x[i] else min_val;
    max_val := if x[i] > max_val then x[i] else max_val;
    i := i + 1;
  }
  result := [min_val, max_val];
}
// </vc-code>
