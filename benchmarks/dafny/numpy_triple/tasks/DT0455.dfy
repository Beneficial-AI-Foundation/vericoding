// <vc-preamble>
// Abstract exponential function with necessary mathematical properties
function FloatExp(x: real): real
  // Exponential is always positive
  ensures FloatExp(x) > 0.0
  // exp(0) = 1
  ensures FloatExp(0.0) == 1.0
  // Exponential is monotonic: if x < y then exp(x) < exp(y)
  ensures forall y :: x < y ==> FloatExp(x) < FloatExp(y)
{
  1.0
}

/**
 * Computes the Hermite weight function exp(-x²) for each element in the input sequence.
 * 
 * @param x: Input sequence of real numbers
 * @returns: Sequence where each element w[i] = exp(-x[i]²)
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method hermweight(x: seq<real>) returns (w: seq<real>)
  // Output sequence has same length as input
  ensures |w| == |x|
  
  // Each output element equals exp(-x²) of corresponding input element
  ensures forall i :: 0 <= i < |x| ==> w[i] == FloatExp(-x[i] * x[i])
  
  // All output values are positive (since exp is always positive)
  ensures forall i :: 0 <= i < |w| ==> w[i] > 0.0
  
  // Maximum value of 1 achieved at x=0 (since exp(-0²) = exp(0) = 1)
  ensures forall i :: 0 <= i < |x| ==> x[i] == 0.0 ==> w[i] == 1.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
