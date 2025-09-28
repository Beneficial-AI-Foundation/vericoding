// <vc-preamble>
// Method to raise a Laguerre series to a specified power
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Predicate to check if all elements in a sequence of reals are zero */
predicate IsZero(s: seq<real>) {
  forall i :: 0 <= i < |s| ==> s[i] == 0.0
}
// </vc-helpers>

// <vc-spec>
method LagPow(c: seq<real>, pow: nat, maxpower: nat) returns (result: seq<real>)
    // Power must be positive
    requires pow > 0
    // Power must not exceed maximum allowed power
    requires pow <= maxpower
    // Maximum power is bounded to prevent unmanageable growth (default limit is 16)
    requires maxpower <= 16
    // Input coefficients sequence must be non-empty
    requires |c| > 0
    
    // Result maintains same length as input coefficient sequence
    ensures |result| == |c|
    // Identity property: raising to power 1 returns the original series
    ensures pow == 1 ==> result == c
    // The coefficients are ordered from low to high degree terms
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix type mismatch in assignment from array to sequence */
{
  var current_pow_coeffs: seq<real> := c;

  if pow == 1 {
    return c;
  }

  var i := 2;
  while i <= pow
    invariant 2 <= i <= pow + 1
    invariant |current_pow_coeffs| == |c|
  {
    var next_pow_coeffs_arr := new real[|c|];
    for k := 0 to |c| - 1 {
      next_pow_coeffs_arr[k] := 0.0;
      for j := 0 to k {
        next_pow_coeffs_arr[k] := next_pow_coeffs_arr[k] + current_pow_coeffs[j] * c[k-j];
      }
    }
    current_pow_coeffs := next_pow_coeffs_arr[..]; // Convert array to sequence
    i := i + 1;
  }
  return current_pow_coeffs;
}
// </vc-code>
