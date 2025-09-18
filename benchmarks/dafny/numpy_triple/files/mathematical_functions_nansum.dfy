// <vc-preamble>
// Looking at the errors, the main issue is with the sequence comprehension syntax on line 64. Dafny's sequence comprehension syntax doesn't support the filter-like syntax being used. I'll fix this by providing a proper sequence construction approach.



// Custom datatype to represent floating point values including NaN and infinities
datatype FloatValue = 
  | Finite(value: real)
  | PosInf
  | NegInf  
  | NaN

// Helper predicates for FloatValue
predicate IsNaN(f: FloatValue) {
  f.NaN?
}

predicate IsFinite(f: FloatValue) {
  f.Finite?
}

predicate IsPositiveInfinity(f: FloatValue) {
  f.PosInf?
}

predicate IsNegativeInfinity(f: FloatValue) {
  f.NegInf?
}

// Helper function to get numeric value for comparison (treating infinities as extreme values)
function GetComparisonValue(f: FloatValue): real
  requires !IsNaN(f)
{
  match f
    case Finite(v) => v
    case PosInf => 1000000.0  // Represent as large positive value
    case NegInf => -1000000.0 // Represent as large negative value
}

// Helper predicate for positive values
predicate IsPositive(f: FloatValue) {
  f.PosInf? || (f.Finite? && f.value > 0.0)
}

// Helper predicate for negative values  
predicate IsNegative(f: FloatValue) {
  f.NegInf? || (f.Finite? && f.value < 0.0)
}

// FloatValue addition with NaN and infinity semantics
function AddFloat(a: FloatValue, b: FloatValue): FloatValue {
  if IsNaN(a) || IsNaN(b) then NaN
  else if IsPositiveInfinity(a) && IsNegativeInfinity(b) then NaN
  else if IsNegativeInfinity(a) && IsPositiveInfinity(b) then NaN
  else if IsPositiveInfinity(a) || IsPositiveInfinity(b) then PosInf
  else if IsNegativeInfinity(a) || IsNegativeInfinity(b) then NegInf
  else Finite(a.value + b.value)
}

// Sum a sequence treating NaN as zero
function SumTreatingNaNAsZero(values: seq<FloatValue>): FloatValue {
  if |values| == 0 then Finite(0.0)
  else
    FoldSum(values, 0)
}

// Recursive helper to sum non-NaN values
function FoldSum(values: seq<FloatValue>, index: nat): FloatValue
  decreases |values| - index
{
  if index >= |values| then Finite(0.0)
  else if IsNaN(values[index]) then FoldSum(values, index + 1)
  else AddFloat(values[index], FoldSum(values, index + 1))
}

// Check if sequence contains positive infinity (ignoring NaN)
predicate ContainsPositiveInfinity(values: seq<FloatValue>) {
  exists i :: 0 <= i < |values| && IsPositiveInfinity(values[i])
}

// Check if sequence contains negative infinity (ignoring NaN) 
predicate ContainsNegativeInfinity(values: seq<FloatValue>) {
  exists i :: 0 <= i < |values| && IsNegativeInfinity(values[i])
}

// Check if all values are NaN
predicate AllValuesAreNaN(values: seq<FloatValue>) {
  forall i :: 0 <= i < |values| ==> IsNaN(values[i])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nansum(a: seq<FloatValue>) returns (result: FloatValue)
  ensures 
    // Core specification: result is the fold sum treating NaN as zero
    result == SumTreatingNaNAsZero(a) &&
    
    // If empty sequence, result is 0
    (|a| == 0 ==> result == Finite(0.0)) &&
    
    // If all elements are NaN, result is 0  
    (AllValuesAreNaN(a) ==> result == Finite(0.0)) &&
    
    // If both positive and negative infinity present (and not all NaN), result is NaN
    (ContainsPositiveInfinity(a) && ContainsNegativeInfinity(a) && !AllValuesAreNaN(a) 
     ==> IsNaN(result)) &&
    
    // If only positive infinity present (and not all NaN), result is positive infinity
    (ContainsPositiveInfinity(a) && !ContainsNegativeInfinity(a) && !AllValuesAreNaN(a)
     ==> IsPositiveInfinity(result)) &&
    
    // If only negative infinity present (and not all NaN), result is negative infinity  
    (!ContainsPositiveInfinity(a) && ContainsNegativeInfinity(a) && !AllValuesAreNaN(a)
     ==> IsNegativeInfinity(result))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
