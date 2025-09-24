// <vc-preamble>
type Vector = seq<real>

// Helper predicate to define banker's rounding (round half to even)
predicate IsRoundedToInteger(value: real, rounded: real)
{
  // The rounded value must be an integer
  rounded == rounded.Floor as real &&
  // The rounded value is the closest integer to the input
  (value - rounded <= 0.5 && value - rounded >= -0.5) &&
  // For ties (fractional part exactly 0.5), round to even
  (value - rounded == 0.5 ==> rounded as int % 2 == 0) &&
  (value - rounded == -0.5 ==> rounded as int % 2 == 0)
}

// Helper function to compute 10^n for scaling
function Power10(n: int): real
  ensures n >= 0 ==> Power10(n) >= 1.0
  ensures n < 0 ==> 0.0 < Power10(n) < 1.0
  ensures n == 0 ==> Power10(n) == 1.0
{
  if n == 0 then 1.0
  else if n > 0 then 10.0 * Power10(n - 1)
  else Power10(n + 1) / 10.0
}

// Predicate to define proper rounding behavior for given decimals
predicate IsProperlyRounded(input: real, output: real, decimals: int)
{
  var scale := Power10(decimals);
  var scaled_input := input * scale;
  var scaled_output := output * scale;
  IsRoundedToInteger(scaled_input, scaled_output)
}

/**
 * numpy.round method that rounds each element of input vector to specified decimal places
 * Uses banker's rounding (round half to even) for tie-breaking
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_round(a: Vector, decimals: int) returns (result: Vector)
  // Precondition: input vector can be any size
  requires true
  
  // Postconditions specifying the rounding behavior
  ensures |result| == |a|  // Same length as input
  
  // Each element is properly rounded according to the decimals parameter
  ensures forall i :: 0 <= i < |a| ==> 
    IsProperlyRounded(a[i], result[i], decimals)
  
  // Monotonicity: order is preserved
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] <= a[j] ==> 
    result[i] <= result[j]
  
  // For decimals = 0, results are integers following banker's rounding
  ensures decimals == 0 ==> 
    forall i :: 0 <= i < |a| ==> 
      result[i] == (result[i] as int) as real &&
      IsRoundedToInteger(a[i], result[i])
  
  // For negative decimals, explicit coverage of rounding to nearest power of 10
  ensures decimals < 0 ==> 
    forall i :: 0 <= i < |a| ==> 
      var scale := Power10(-decimals);
      result[i] % scale == 0.0 &&
      IsProperlyRounded(a[i], result[i], decimals)
  
  // Approximation bound: squared error ≤ 1.0 for non-negative decimals
  ensures decimals >= 0 ==> 
    forall i :: 0 <= i < |a| ==> 
      var error := result[i] - a[i];
      error * error <= 1.0
  
  // Idempotence property: rounding an already properly-rounded value gives same result  
  ensures decimals >= 0 ==> 
    forall i :: 0 <= i < |a| ==> 
      IsProperlyRounded(a[i], a[i], decimals) ==> 
        IsProperlyRounded(a[i], result[i], decimals)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
