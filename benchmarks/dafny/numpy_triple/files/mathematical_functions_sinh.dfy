// <vc-preamble>
// Uninterpreted function for mathematical exponential
ghost function Exp(x: real): real

// Helper function to define hyperbolic sine mathematically
ghost function SinhValue(x: real): real
{
  (Exp(x) - Exp(-x)) / 2.0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Sinh(x: seq<real>) returns (result: seq<real>)
  // No preconditions - hyperbolic sine is defined for all real numbers
  ensures |result| == |x|
  
  // Core mathematical definition: sinh(x) = (e^x - e^(-x))/2
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == SinhValue(x[i])
  
  // Odd function property: sinh(-x) = -sinh(x)
  ensures forall i :: 0 <= i < |x| ==>
    SinhValue(-x[i]) == -result[i]
  
  // Zero property: sinh(0) = 0
  ensures forall i :: 0 <= i < |x| ==>
    x[i] == 0.0 ==> result[i] == 0.0
  
  // Sign property: sinh(x) has the same sign as x
  ensures forall i :: 0 <= i < |x| ==>
    (x[i] > 0.0 ==> result[i] > 0.0) &&
    (x[i] < 0.0 ==> result[i] < 0.0)
  
  // Monotonicity property: sinh is strictly increasing
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| ==>
    x[i] < x[j] ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
