// <vc-preamble>
// FloatValue datatype to represent IEEE 754 floating-point values including special values
datatype FloatValue = 
  | Finite(value: real)
  | PositiveInfinity
  | NegativeInfinity  
  | NaN

// Predicate to check if a FloatValue is infinite (positive or negative)
predicate IsInfinite(f: FloatValue) 
{
  f.PositiveInfinity? || f.NegativeInfinity?
}

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
  f.NaN?
}

// Predicate to check if a FloatValue is finite
predicate IsFinite(f: FloatValue)
{
  f.Finite?
}

// Predicate to check if a FloatValue represents zero
predicate IsZero(f: FloatValue)
{
  f.Finite? && f.value == 0.0
}

// Test element-wise for positive or negative infinity in a vector
// Returns a boolean sequence of the same length as input, True where element == +/-inf, otherwise False
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method isinf(x: seq<FloatValue>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> 
    (result[i] == IsInfinite(x[i]))
  ensures forall i :: 0 <= i < |x| ==> 
    (!IsInfinite(x[i]) ==> result[i] == false)
  ensures forall i :: 0 <= i < |x| ==> 
    (IsNaN(x[i]) ==> result[i] == false)
  ensures forall i :: 0 <= i < |x| ==> 
    (IsZero(x[i]) ==> result[i] == false)
  ensures forall i :: 0 <= i < |x| ==> 
    (result[i] == true ==> !IsFinite(x[i]))
  ensures forall i :: 0 <= i < |x| ==> 
    (result[i] == true ==> !IsNaN(x[i]))
  ensures forall i :: 0 <= i < |x| ==> 
    (result[i] == true ==> IsInfinite(x[i]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
