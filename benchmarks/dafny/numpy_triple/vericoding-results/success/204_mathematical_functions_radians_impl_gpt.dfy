// <vc-preamble>
/*
 * Dafny specification for numpy.radians functionality.
 * Converts angles from degrees to radians element-wise using the formula: radians = degrees * π / 180
 * Maintains array shape and provides element-wise mapping from degree values to radian values.
 */

// Mathematical constant π approximation for conversion calculations
const PI: real := 3.141592653589793
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): elementary degree-to-radian conversion */
function deg_to_rad(d: real): real { d * PI / 180.0 }

/* helper modified by LLM (iteration 2): build a sequence of radians from degrees preserving length and element-wise mapping */
function seq_map_radians(n: nat, x: seq<real>): seq<real>
  requires |x| == n
  ensures |seq_map_radians(n, x)| == n
  ensures forall i :: 0 <= i < n ==> seq_map_radians(n, x)[i] == deg_to_rad(x[i])
  decreases n
{
  if n == 0 then []
  else
    seq_map_radians(n - 1, x[..n-1]) + [deg_to_rad(x[n - 1])]
}
// </vc-helpers>

// <vc-spec>
method numpy_radians(n: nat, x: seq<real>) returns (result: seq<real>)
    // Input must be a fixed-size vector of length n
    requires |x| == n
    // Postcondition: result has the same fixed size n as input
    ensures |result| == n
    // Each element is converted from degrees to radians using the formula: radians = degrees * π / 180
    ensures forall i :: 0 <= i < n ==> result[i] == x[i] * PI / 180.0
    // Mathematical properties: specific angle conversions are preserved
    ensures forall i :: 0 <= i < n ==> 
        (x[i] == 0.0 ==> result[i] == 0.0) // 0 degrees = 0 radians
    // 180 degrees approximately equals π radians (within reasonable floating point precision)
    ensures forall i :: 0 <= i < n ==> 
        (x[i] == 180.0 ==> result[i] > 3.14 && result[i] < 3.15)
    // 360 degrees approximately equals 2π radians (within reasonable floating point precision)
    ensures forall i :: 0 <= i < n ==> 
        (x[i] == 360.0 ==> result[i] > 6.28 && result[i] < 6.29)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct the result via a verified recursive sequence builder */
  result := seq_map_radians(n, x);
}
// </vc-code>
