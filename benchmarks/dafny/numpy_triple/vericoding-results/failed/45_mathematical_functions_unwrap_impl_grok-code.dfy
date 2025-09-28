// <vc-preamble>
/*
 * Phase unwrapping functionality for correcting discontinuities in phase data.
 * Unwraps radian phase by changing absolute jumps greater than discont to their 2*pi complement.
 * For consecutive elements with difference > discont, adds/subtracts multiples of period to create continuity.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax in exists clause by removing redundant | true */
function ComputeAdjusted(diff: real, period: real, discont: real): real
  requires period > 0.0
  requires discont > 0.0
  ensures |ComputeAdjusted(diff, period, discont)| <= discont
  ensures exists k: real :: diff - ComputeAdjusted(diff, period, discont) = k * period
{
  if -discont < diff && diff <= discont then
    diff
  else if diff >= discont then
    ComputeAdjusted(diff - period, period, discont)
  else
    ComputeAdjusted(diff + period, period, discont)
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
/* code modified by LLM (iteration 5): implementation appears correct after helper fix */
{
  if |p| == 0 {
    result := [];
  } else {
    result := [p[0]];
    var current := 1;
    while current < |p|
      decreases |p| - current
      invariant 1 <= current <= |p|
      invariant |result| == current
      invariant result[0] == p[0]
      invariant forall i :: 0 <= i < |result| ==> exists k : real | result[i] == p[i] + k * period
      invariant forall j :: 0 <= j < current - 1 ==>
        (if result[j+1] - result[j] >= 0.0 then result[j+1] - result[j] <= discont
         else result[j] - result[j+1] <= discont)
    {
      var diff := p[current] - result[current - 1];
      var adjusted := ComputeAdjusted(diff, period, discont);
      result := result + [result[current - 1] + adjusted];
      current := current + 1;
    }
  }
}
// </vc-code>
