// <vc-preamble>
// Helper predicates for floating-point special values
predicate IsFinite(x: real) {
  // For mathematical reals, all finite values are considered finite
  true
}

predicate IsNaN(x: real) {
  // Mathematical reals don't have NaN
  false
}

predicate IsInf(x: real) {
  // Mathematical reals don't have infinity in IEEE 754 sense
  false
}

// Helper function to get absolute value
function Abs(x: real): real {
  if x >= 0.0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Spacing(x: seq<real>) returns (result: seq<real>)
  requires true // Spacing is defined for all floating-point inputs
  ensures |result| == |x| // Output array has same size as input
  ensures forall i :: 0 <= i < |x| ==> (
    // For finite values, spacing is always positive
    (IsFinite(x[i]) && !IsNaN(x[i]) ==> result[i] > 0.0) &&
    
    // For infinity or NaN inputs, result is NaN
    ((IsInf(x[i]) || IsNaN(x[i])) ==> IsNaN(result[i]))
  )
  ensures forall i, j :: (0 <= i < |x| && 0 <= j < |x| && 
    IsFinite(x[i]) && !IsNaN(x[i]) && IsFinite(x[j]) && !IsNaN(x[j]) &&
    Abs(x[i]) == Abs(x[j])) ==> result[i] == result[j] // Magnitude-based equivalence
  ensures forall i :: (0 <= i < |x| && IsFinite(x[i]) && !IsNaN(x[i])) ==> 
    (exists j :: 0 <= j < |x| && x[j] == -x[i] && IsFinite(x[j]) && !IsNaN(x[j]) ==> 
     result[i] == result[j]) // Symmetry property: spacing(-x) = spacing(x)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
