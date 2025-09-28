// <vc-preamble>
// Method to compute the domain (smallest interval) containing all input points
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' for compliance and defined min over reals */
function minReal(a: real, b: real): real {
  if a <= b then a else b
}

/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' for compliance and defined max over reals */
function maxReal(a: real, b: real): real {
  if a >= b then a else b
}
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
  /* code modified by LLM (iteration 2): implemented single-pass min/max scan with invariants ensuring bounds and existence */
  var minVal: real := x[0];
  var maxVal: real := x[0];
  var minIdx: int := 0;
  var maxIdx: int := 0;
  var i: int := 1;
  while i < |x|
    invariant 1 <= i <= |x|
    invariant 0 <= minIdx < i
    invariant 0 <= maxIdx < i
    invariant minVal == x[minIdx]
    invariant maxVal == x[maxIdx]
    invariant minVal <= maxVal
    invariant forall j :: 0 <= j < i ==> minVal <= x[j] <= maxVal
    decreases |x| - i
  {
    if x[i] < minVal {
      minVal := x[i];
      minIdx := i;
    }
    if x[i] > maxVal {
      maxVal := x[i];
      maxIdx := i;
    }
    i := i + 1;
  }
  result := [minVal, maxVal];
}
// </vc-code>
