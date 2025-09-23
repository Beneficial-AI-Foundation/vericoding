// <vc-preamble>
// Built-in trigonometric functions - assumed to be available
function {:extern} Sin(x: real): real
function {:extern} Arcsin(x: real): real

// Mathematical constants
const PI: real := 3.141592653589793
const HALF_PI: real := 1.5707963267948966

// Specification for the inverse relationship between sin and arcsin
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
lemma {:axiom} SinArcsin_Inverse(x: real)
  requires -1.0 <= x <= 1.0
  ensures Sin(Arcsin(x)) == x

// Specification for arcsin range
lemma {:axiom} Arcsin_Range(x: real)
  requires -1.0 <= x <= 1.0
  ensures -HALF_PI <= Arcsin(x) <= HALF_PI

// Specification for arcsin monotonicity
lemma {:axiom} Arcsin_Monotonic(x: real, y: real)
  requires -1.0 <= x <= 1.0
  requires -1.0 <= y <= 1.0
  requires x <= y
  ensures Arcsin(x) <= Arcsin(y)

// Specification for special values
lemma {:axiom} Arcsin_SpecialValues()
  ensures Arcsin(0.0) == 0.0
  ensures Arcsin(1.0) == HALF_PI
  ensures Arcsin(-1.0) == -HALF_PI

/**
 * Computes the inverse sine of each element in the input sequence.
 * For real arguments, the domain is [-1, 1] and the range is [-π/2, π/2].
 */
method numpy_arcsin(x: seq<real>) returns (result: seq<real>)
  // Precondition: All elements must be in domain [-1, 1]
  requires forall i :: 0 <= i < |x| ==> -1.0 <= x[i] <= 1.0
  
  // Postcondition: Output has same length as input
  ensures |result| == |x|
  
  // Postcondition: Each element is arcsin of corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == Arcsin(x[i])
  
  // Postcondition: All results are in valid range [-π/2, π/2]
  ensures forall i :: 0 <= i < |result| ==> -HALF_PI <= result[i] <= HALF_PI
  
  // Postcondition: Inverse relationship holds (sin(arcsin(x)) = x)
  ensures forall i :: 0 <= i < |x| ==> Sin(result[i]) == x[i]
  
  // Postcondition: Monotonicity property
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] <= x[j] ==> result[i] <= result[j]
  
  // Postcondition: Special values
  ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==> result[i] == 0.0
  ensures forall i :: 0 <= i < |x| && x[i] == 1.0 ==> result[i] == HALF_PI
  ensures forall i :: 0 <= i < |x| && x[i] == -1.0 ==> result[i] == -HALF_PI
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
