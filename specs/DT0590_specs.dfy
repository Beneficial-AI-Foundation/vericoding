// <vc-preamble>
// Represents a floating point value that can be either a real number or NaN
datatype FloatValue = Real(value: real) | NaN

// Helper predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Helper predicate to check if a FloatValue is a real number
predicate IsReal(f: FloatValue) {
    f.Real?
}

// Helper function to compare two real FloatValues
predicate LessOrEqual(a: FloatValue, b: FloatValue) 
  requires IsReal(a) && IsReal(b)
{
  a.value <= b.value
}

/**
 * Returns the maximum value in a non-empty sequence, ignoring NaN values.
 * If all values are NaN, returns NaN.
 * If at least one value is not NaN, returns the maximum non-NaN value.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanmax(a: seq<FloatValue>) returns (result: FloatValue)
  requires |a| > 0
  // Case 1: If there exists at least one non-NaN element, result is maximum of non-NaN elements
  ensures (exists i: int :: 0 <= i < |a| && IsReal(a[i])) ==> (
    IsReal(result) && 
    (exists max_idx: int :: 0 <= max_idx < |a| && 
      result == a[max_idx] && 
      IsReal(a[max_idx]) &&
      (forall j: int :: 0 <= j < |a| && IsReal(a[j]) ==> LessOrEqual(a[j], result)))
  )
  // Case 2: If all elements are NaN, result is NaN
  ensures (forall i: int :: 0 <= i < |a| ==> IsNaN(a[i])) ==> IsNaN(result)
  // Case 3: NaN values are ignored - if result is not NaN, it's the max of non-NaN elements
  ensures IsReal(result) ==> (
    exists witness: int :: 0 <= witness < |a| && 
    result == a[witness] && 
    IsReal(a[witness]) &&
    (forall j: int :: 0 <= j < |a| && IsReal(a[j]) ==> LessOrEqual(a[j], result))
  )
  // Case 4: For sequences without NaN, behaves like regular max
  ensures (forall i: int :: 0 <= i < |a| ==> IsReal(a[i])) ==> (
    IsReal(result) &&
    (exists max_idx: int :: 0 <= max_idx < |a| &&
      result == a[max_idx] &&
      (forall j: int :: 0 <= j < |a| ==> LessOrEqual(a[j], result)))
  )
  // Sanity check: result is either NaN or exists in the sequence
  ensures IsNaN(result) || (exists witness: int :: 0 <= witness < |a| && result == a[witness])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
