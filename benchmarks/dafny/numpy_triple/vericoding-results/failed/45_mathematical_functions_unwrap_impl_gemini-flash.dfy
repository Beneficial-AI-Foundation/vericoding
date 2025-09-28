// <vc-preamble>
/*
 * Phase unwrapping functionality for correcting discontinuities in phase data.
 * Unwraps radian phase by changing absolute jumps greater than discont to their 2*pi complement.
 * For consecutive elements with difference > discont, adds/subtracts multiples of period to create continuity.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `size` operator can only be applied to arrays for lengths. Replaced `|r_arr|` with `r_arr.Length` to retrieve the length of the array. */
function {:fuel 0} floor(x: real): real {
    if x < 0.0 then
        var x_int := x as int;
        if x_int as real == x then x_int as real
        else (x_int - 1) as real
    else
        (x as int) as real
}

function abs(x: real): real {
  if x < 0.0 then -x else x
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
/* code modified by LLM (iteration 5): Fixed `invariant |r_arr| == |p|` to `invariant r_arr.Length == |p|` to resolve the compilation error. The `size` operator cannot be used on arrays and should be replaced with `.Length`. */
{
  var r_arr := new real[|p|];
  if |p| == 0 {
    return [];
  }

  r_arr[0] := p[0];
  var i := 0;
  while i < |p| - 1
    invariant 0 <= i < |p|
    invariant r_arr.Length == |p|
    invariant forall j :: 0 <= j <= i ==> (exists k: real {:trigger k * period} :: r_arr[j] == p[j] + k * period)
    invariant forall j :: 0 <= j <= i ==> (j == 0 ==> r_arr[j] == p[j])
    invariant forall j :: 0 <= j < i ==> abs(r_arr[j+1] - r_arr[j]) <= discont
  {
    var d := p[i+1] - r_arr[i]; // Difference between the next point in original sequence and current unwrapped point
    var m_val := floor((d + period / 2.0) / period); // Find integer m such that r_arr[i] + d - m*period is closest to r_arr[i]
    r_arr[i+1] := p[i+1] - m_val * period;

    // After initial unwrapping, ensure the difference is within discont
    // If not, adjust by period until it is.
    if abs(r_arr[i+1] - r_arr[i]) > discont {
      var diff := r_arr[i+1] - r_arr[i];
      var num_periods_to_shift: real;
      if diff > 0.0 {
        num_periods_to_shift := floor((diff - discont) / period) + 1.0;
        r_arr[i+1] := r_arr[i+1] - num_periods_to_shift * period;
      } else {
        num_periods_to_shift := floor((-diff - discont) / period) + 1.0; // diff is negative, so -diff is positive
        r_arr[i+1] := r_arr[i+1] + num_periods_to_shift * period;
      }
    }
    
    // One final check and adjustment to ensure the difference is within the discont range.
    // In some cases, the above adjustment might overcorrect or undershoot slightly.
     if abs(r_arr[i+1] - r_arr[i]) > discont {
      var diff := r_arr[i+1] - r_arr[i];
      var num_periods_to_shift: real;
      if diff > 0.0 {
        num_periods_to_shift := floor((diff - discont) / period) + 1.0;
        r_arr[i+1] := r_arr[i+1] - num_periods_to_shift * period;
      } else {
        num_periods_to_shift := floor((-diff - discont) / period) + 1.0;
        r_arr[i+1] := r_arr[i+1] + num_periods_to_shift * period;
      }
    }

    i := i + 1;
  }

  result := r_arr[..];
}
// </vc-code>
