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
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x[j] * PI / 180.0
  {
    result := result + [x[i] * PI / 180.0];
    i := i + 1;
  }
}
// </vc-code>
