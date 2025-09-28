// <vc-preamble>
/*
 * Phase unwrapping functionality for correcting discontinuities in phase data.
 * Unwraps radian phase by changing absolute jumps greater than discont to their 2*pi complement.
 * For consecutive elements with difference > discont, adds/subtracts multiples of period to create continuity.
 */
// </vc-preamble>

// <vc-helpers>
function abs(x: real): real {
  if x >= 0.0 then x else -x
}

function floor(x: real): (r: int)
  ensures r as real <= x < r as real + 1.0
{
  x.Floor
}

function round(x: real): (r: real)
  ensures abs(x - r) <= 0.5
  ensures r == (r.Floor as real)
{
  (x + 0.5).Floor as real
}

/* helper modified by LLM (iteration 4): Replaced unbounded quantifier with a compilable arithmetic check. */
predicate IsIntMultipleApart(x: real, y: real, period: real)
  requires period > 0.0
{
  var k_real := (x - y) / period;
  k_real == floor(k_real) as real
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
  /* code modified by LLM (iteration 4): [No logic change, helper fix addresses compilation error] */
  if |p| < 1 {
    result := [];
  } else {
    var res_arr := new real[|p|];
    res_arr[0] := p[0];
    var i := 1;
    while i < |p|
      invariant 1 <= i <= |p|
      invariant res_arr.Length == |p|
      invariant |p| > 0 ==> res_arr[0] == p[0]
      invariant forall j :: 0 <= j < i ==> IsIntMultipleApart(res_arr[j], p[j], period)
      invariant forall j :: 0 <= j < i - 1 ==> abs(res_arr[j+1] - res_arr[j]) <= discont
    {
      var prev_val := res_arr[i-1];
      var val := p[i];
      
      var diff := val - prev_val;

      if diff > discont {
        var n := round((diff - discont) / period) + 1.0;
        val := val - n * period;
      } else if diff < -discont {
        var n := round((diff + discont) / period) - 1.0;
        val := val - n * period;
      }
      
      res_arr[i] := val;
      i := i + 1;
    }
    result := res_arr[..];
  }
}
// </vc-code>
