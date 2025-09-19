// <vc-preamble>
// Datatype to represent floating point values that can be NaN
datatype FloatValue = Real(val: real) | NaN

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
  f.NaN?
}

// Predicate to check if a FloatValue is a valid (non-NaN) real number
predicate IsReal(f: FloatValue) {
  f.Real?
}

// Extract real value from FloatValue (only valid when IsReal)
function GetRealValue(f: FloatValue): real
  requires IsReal(f)
{
  f.val
}

// Get indices of valid (non-NaN) elements in the array
function GetValidIndices(a: array<FloatValue>): set<int>
  reads a
{
  set i | 0 <= i < a.Length && IsReal(a[i])
}

// Count of valid (non-NaN) elements
function ValidCount(a: array<FloatValue>): nat
  reads a
{
  |GetValidIndices(a)|
}

// Sum of valid elements
function SumValidElements(a: array<FloatValue>): real
  reads a
{
  if ValidCount(a) == 0 then 0.0
  else 
    // This is a simplified representation - in practice would need proper summation
    0.0 // Placeholder for the actual sum computation
}

// Mean of valid elements
function MeanValidElements(a: array<FloatValue>): real
  reads a
  requires ValidCount(a) > 0
{
  SumValidElements(a) / (ValidCount(a) as real)
}

// Sum of squared deviations from mean for valid elements
function SumSquaredDeviations(a: array<FloatValue>, mean: real): real
  reads a
  requires ValidCount(a) > 0
{
  var validIndices := GetValidIndices(a);
  // Sum of (x_i - mean)^2 for all valid elements
  // Simplified representation - would need proper summation in implementation
  0.0 // Placeholder for the actual sum computation
}

// Square root function (mathematical)
function Sqrt(x: real): real
  requires x >= 0.0
{
  0.0 // Placeholder implementation
}

// Main method to compute standard deviation ignoring NaNs
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanstd(a: array<FloatValue>, ddof: nat) returns (result: FloatValue)
  requires a.Length >= 0
  requires ddof >= 0
  ensures 
    var validCount := ValidCount(a);
    if validCount > 0 && ddof < validCount then
      // Case 1: Valid computation possible
      IsReal(result) && 
      GetRealValue(result) >= 0.0 &&
      (validCount > ddof ==> 
        var mean := MeanValidElements(a);
        var variance := SumSquaredDeviations(a, mean) / ((validCount - ddof) as real);
        GetRealValue(result) == Sqrt(variance)
      )
    else
      // Case 2: Not enough valid data or all NaN
      IsNaN(result)
  ensures
    // Additional property: result is never negative when valid
    IsReal(result) ==> GetRealValue(result) >= 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
