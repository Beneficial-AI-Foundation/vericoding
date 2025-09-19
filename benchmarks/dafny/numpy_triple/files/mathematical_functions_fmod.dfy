// <vc-preamble>
/*
 * Element-wise remainder of division (fmod) operation on sequences of real numbers.
 * Returns the remainder with the same sign as the dividend, following C library fmod semantics.
 */

// Datatype to represent either a real number or NaN (not-a-number)
datatype FloatValue = Real(value: real) | NaN

// Helper predicate to check if a FloatValue represents NaN
predicate IsNaN(x: FloatValue) {
    x.NaN?
}

// Helper function to get real value from FloatValue (only valid for Real case)
function GetReal(x: FloatValue): real
    requires x.Real?
{
    x.value
}

// Helper function for absolute value of FloatValue
function Abs(x: FloatValue): real
    requires x.Real?
{
    if x.value >= 0.0 then x.value else -x.value
}

// Helper function to determine sign of a real number
function Sign(x: real): int {
    if x > 0.0 then 1 else if x < 0.0 then -1 else 0
}

// Helper predicate for truncated division towards zero
predicate IsTruncatedQuotient(dividend: real, divisor: real, quotient: real)
    requires divisor != 0.0
{
    // quotient is the result of truncating dividend/divisor towards zero
    var exactQuotient := dividend / divisor;
    if exactQuotient >= 0.0 then
        // For positive quotients, truncate by taking floor
        quotient == RealFloor(exactQuotient)
    else
        // For negative quotients, truncate by taking ceiling
        quotient == RealCeil(exactQuotient)
}

// Floor function - returns largest integer less than or equal to x
function RealFloor(x: real): real
{
    x as int as real
}

// Ceiling function - returns smallest integer greater than or equal to x  
function RealCeil(x: real): real
{
    if x == (x as int as real) then x else (x as int as real) + 1.0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FMod(x1: seq<FloatValue>, x2: seq<FloatValue>) returns (result: seq<FloatValue>)
    requires |x1| == |x2|
    ensures |result| == |x1|
    ensures forall i :: 0 <= i < |x1| ==>
        // When divisor is NaN or dividend is NaN, result is NaN
        (IsNaN(x1[i]) || IsNaN(x2[i]) ==> IsNaN(result[i])) &&
        // When divisor is zero (and not NaN), result is NaN
        (x2[i].Real? && x2[i].value == 0.0 ==> IsNaN(result[i])) &&
        // When both operands are real and divisor is non-zero
        (x1[i].Real? && x2[i].Real? && x2[i].value != 0.0 ==> 
            result[i].Real? &&
            // There exists a truncated quotient k such that result = x1 - k * x2
            (exists k: real :: 
                IsTruncatedQuotient(x1[i].value, x2[i].value, k) &&
                result[i].value == x1[i].value - k * x2[i].value) &&
            // The remainder has the same sign as the dividend x1 (or is zero)
            (result[i].value != 0.0 ==> Sign(result[i].value) == Sign(x1[i].value)) &&
            // The absolute value of remainder is less than absolute value of divisor
            Abs(result[i]) < Abs(x2[i]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
