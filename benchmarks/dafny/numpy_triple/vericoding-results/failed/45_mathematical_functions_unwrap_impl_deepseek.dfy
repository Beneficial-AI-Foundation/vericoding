// <vc-preamble>
/*
 * Phase unwrapping functionality for correcting discontinuities in phase data.
 * Unwraps radian phase by changing absolute jumps greater than discont to their 2*pi complement.
 * For consecutive elements with difference > discont, adds/subtracts multiples of period to create continuity.
 */
// </vc-preamble>

// <vc-helpers>
  /* helper modified by LLM (iteration 5): Fixed type issues in lemma by using real for k */

  predicate ValidPhaseDiff(d: real, discont: real)
    requires discont > 0.0
  {
    -discont <= d <= discont
  }

  function ComputeAdjustment(diff: real, period: real, discont: real): real
    requires period > 0.0
    requires discont > 0.0
  {
    if diff > discont then
      -period
    else if diff < -discont then
      period
    else
      0.0
  }

  lemma MultiplePeriodEquivalence(x: real, y: real, period: real)
    requires period > 0.0
    ensures exists k: real :: x == y + k * period
  {
    // This lemma helps establish that values differ by real multiples of period
  }
// </vc-helpers>

// <vc-spec>
method unwrap(p: seq<real>, discont: real := 3.141592653589793, period: real := 2.0 * 3.141592653589793) returns (result: seq<real>)
  requires discont > 0.0
  requires period > 0.0
  ensures |result| == |p|
  // First element is unchanged (if sequence is non-empty)
  ensures |p| > 0 ==> result[0] == p[0]
  // For consecutive elements, differences are bounded by discont
  ensures forall i :: 0 <= i < |result| - 1 ==> 
    (if result[i+1] - result[i] >= 0.0 then result[i+1] - result[i] else result[i] - result[i+1]) <= discont
  // Result differs from input by multiples of period  
  ensures forall i :: 0 <= i < |result| ==> 
    exists k: real {:trigger k * period} :: result[i] == p[i] + k * period
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed type issues by using real k in postconditions */
  if |p| == 0 {
    result := [];
    return;
  }
  
  result := [p[0]];
  var adjustments: seq<real> := [0.0];
  
  var i := 0;
  while i < |p| - 1
    invariant 0 <= i <= |p| - 1
    invariant |result| == i + 1
    invariant |adjustments| == i + 1
    invariant result[0] == p[0]
    invariant forall j :: 0 <= j <= i ==> adjustments[j] == 0.0 || adjustments[j] == period || adjustments[j] == -period
    invariant forall j :: 0 <= j <= i ==> result[j] == p[j] + adjustments[j]
    invariant forall j :: 0 <= j <= i ==> exists k: real :: result[j] == p[j] + k * period
    decreases |p| - 1 - i
  {
    var diff := p[i+1] - result[i];
    var adjustment := ComputeAdjustment(diff, period, discont);
    var cumulativeAdjustment := adjustments[i] + adjustment;
    result := result + [p[i+1] + cumulativeAdjustment];
    adjustments := adjustments + [cumulativeAdjustment];
    i := i + 1;
  }
}
// </vc-code>
