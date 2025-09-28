// <vc-preamble>
/*
 * Phase unwrapping functionality for correcting discontinuities in phase data.
 * Unwraps radian phase by changing absolute jumps greater than discont to their 2*pi complement.
 * For consecutive elements with difference > discont, adds/subtracts multiples of period to create continuity.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Helper functions for phase unwrapping */
function abs(x: real): real
{
  if x >= 0.0 then x else -x
}

function roundToNearest(x: real): int
{
  if x >= 0.0 then 
    if x - x.Floor as real < 0.5 then x.Floor else x.Floor + 1
  else
    if x.Floor as real - x < 0.5 then x.Floor else x.Floor - 1
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
/* code modified by LLM (iteration 5): Implement unwrapping by adjusting each element based on difference from previous */
{
  if |p| == 0 {
    return [];
  }
  
  result := [p[0]];
  var i := 1;
  
  while i < |p|
    invariant 1 <= i <= |p|
    invariant |result| == i
    invariant result[0] == p[0]
    invariant forall j :: 0 <= j < i - 1 ==> abs(result[j+1] - result[j]) <= discont
    invariant forall j :: 0 <= j < i ==> exists k: real {:trigger k * period} :: result[j] == p[j] + k * period
  {
    var diff := p[i] - result[i-1];
    var adjusted_value := p[i];
    
    if diff > discont {
      // Jump is too large positive, subtract period multiples
      var n := roundToNearest((diff - discont) / period);
      adjusted_value := p[i] - (n as real) * period;
    } else if diff < -discont {
      // Jump is too large negative, add period multiples  
      var n := roundToNearest((-diff - discont) / period);
      adjusted_value := p[i] + (n as real) * period;
    }
    
    result := result + [adjusted_value];
    i := i + 1;
  }
}
// </vc-code>
