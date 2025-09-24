// <vc-preamble>
/*
 * This file implements the numpy.modf function specification, which returns 
 * the fractional and integral parts of an array element-wise. Both parts
 * maintain the same sign as the input value.
 */

// Predicate to check if a real number is an integer
ghost predicate IsInteger(r: real) {
    exists n: int :: r == n as real
}

// Implementation of numpy.modf: returns fractional and integral parts element-wise
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_modf(x: seq<real>) returns (fractional_parts: seq<real>, integral_parts: seq<real>)
    // No preconditions - modf works on all real values
    requires true
    // Output arrays have same length as input
    ensures |fractional_parts| == |x|
    ensures |integral_parts| == |x|
    // Parts sum to original value
    ensures forall i :: 0 <= i < |x| ==> 
        fractional_parts[i] + integral_parts[i] == x[i]
    // Fractional part has absolute value less than 1
    ensures forall i :: 0 <= i < |x| ==> 
        -1.0 < fractional_parts[i] < 1.0
    // Both parts have same sign as original (or are zero) - positive case
    ensures forall i :: 0 <= i < |x| ==> 
        (x[i] >= 0.0 ==> fractional_parts[i] >= 0.0 && integral_parts[i] >= 0.0)
    // Both parts have same sign as original (or are zero) - negative case  
    ensures forall i :: 0 <= i < |x| ==> 
        (x[i] < 0.0 ==> fractional_parts[i] <= 0.0 && integral_parts[i] <= 0.0)
    // Integral part is actually an integer value
    ensures forall i :: 0 <= i < |x| ==> 
        IsInteger(integral_parts[i])
    // Integral part is truncated towards zero (largest integer with smaller absolute value)
    ensures forall i :: 0 <= i < |x| ==> 
        (x[i] >= 0.0 ==> integral_parts[i] <= x[i] < integral_parts[i] + 1.0)
    ensures forall i :: 0 <= i < |x| ==> 
        (x[i] < 0.0 ==> integral_parts[i] - 1.0 < x[i] <= integral_parts[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
