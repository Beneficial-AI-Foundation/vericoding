// <vc-preamble>
/*
 * Phase unwrapping functionality for correcting discontinuities in phase data.
 * Unwraps radian phase by changing absolute jumps greater than discont to their 2*pi complement.
 * For consecutive elements with difference > discont, adds/subtracts multiples of period to create continuity.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed postcondition proofs with explicit witnesses */
function abs(x: real): real {
  if x >= 0.0 then x else -x
}

function adjustPhase(p_val: real, prev_result: real, discont: real, period: real): real
  requires discont > 0.0
  requires period > 0.0
  ensures exists k: real {:trigger k * period} :: adjustPhase(p_val, prev_result, discont, period) == p_val + k * period
  ensures abs(adjustPhase(p_val, prev_result, discont, period) - prev_result) <= discont
{
  var diff := p_val - prev_result;
  if diff > discont then 
    assert p_val - period == p_val + (-1.0) * period;
    p_val - period
  else if diff < -discont then 
    assert p_val + period == p_val + 1.0 * period;
    p_val + period
  else 
    assert p_val == p_val + 0.0 * period;
    p_val
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
  /* code modified by LLM (iteration 5): fixed loop invariant initialization */
  if |p| == 0 {
    result := [];
    return;
  }
  
  result := [p[0]];
  assert result[0] == p[0] + 0.0 * period;
  var i := 1;
  
  while i < |p|
    invariant 1 <= i <= |p|
    invariant |result| == i
    invariant result[0] == p[0]
    invariant forall j :: 0 <= j < i - 1 ==> abs(result[j+1] - result[j]) <= discont
    invariant forall j :: 0 <= j < i ==> exists k: real {:trigger k * period} :: result[j] == p[j] + k * period
  {
    var corrected := adjustPhase(p[i], result[i-1], discont, period);
    result := result + [corrected];
    i := i + 1;
  }
}
// </vc-code>
