// <vc-preamble>
/*
 * Test element-wise for positive infinity, return result as bool array.
 * This module implements numpy.isposinf functionality for detecting positive infinity
 * values in floating-point arrays according to IEEE 754 standard.
 */

// Float datatype representing IEEE 754 floating-point values including special values
datatype Float = 
  | Finite(value: real)
  | PosInf
  | NegInf  
  | NaN

// Predicate to check if a Float is positive infinity
predicate IsPositiveInfinity(f: Float)
{
  f.PosInf?
}

// Predicate to check if a Float is negative infinity
predicate IsNegativeInfinity(f: Float)
{
  f.NegInf?
}

// Predicate to check if a Float is any infinity (positive or negative)
predicate IsInf(f: Float)
{
  f.PosInf? || f.NegInf?
}

// Predicate to check if a Float is NaN
predicate IsNaN(f: Float)
{
  f.NaN?
}

// Predicate to check if a Float is finite
predicate IsFinite(f: Float)
{
  f.Finite?
}

// Comparison predicates for Float values
predicate FloatGreaterThanZero(f: Float)
{
  match f
    case Finite(v) => v > 0.0
    case PosInf => true
    case NegInf => false
    case NaN => false
}

predicate FloatLessThanZero(f: Float)
{
  match f
    case Finite(v) => v < 0.0
    case PosInf => false
    case NegInf => true
    case NaN => false
}

predicate FloatEqualsZero(f: Float)
{
  match f
    case Finite(v) => v == 0.0
    case PosInf => false
    case NegInf => false
    case NaN => false
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPositiveInfinityArray(x: seq<Float>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> 
    // Primary property: result is true iff input is positive infinity
    (result[i] == IsPositiveInfinity(x[i])) &&
    // Sanity checks: finite values return false
    (!IsInf(x[i]) ==> result[i] == false) &&
    // Negative infinity returns false
    (IsNegativeInfinity(x[i]) ==> result[i] == false) &&
    // NaN is not positive infinity
    (IsNaN(x[i]) ==> result[i] == false) &&
    // Zero is not positive infinity
    (FloatEqualsZero(x[i]) ==> result[i] == false) &&
    // Mathematical property: if result is true, then x is positive infinity
    (result[i] == true ==> IsPositiveInfinity(x[i])) &&
    // Exclusivity: cannot be both positive infinity and NaN
    (result[i] == true ==> !IsNaN(x[i])) &&
    // Exclusivity: cannot be both positive infinity and negative infinity
    (result[i] == true ==> !IsNegativeInfinity(x[i])) &&
    // Exclusivity: cannot be both positive infinity and finite
    (result[i] == true ==> !IsFinite(x[i]))
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == IsPositiveInfinity(x[j])
  {
    result := result + [IsPositiveInfinity(x[i])];
  }
}
// </vc-code>
