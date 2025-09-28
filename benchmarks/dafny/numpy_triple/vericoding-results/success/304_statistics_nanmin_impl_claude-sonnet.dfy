// <vc-preamble>
// Model floating point values that can be NaN
datatype Float = Real(value: real) | NaN

// Predicate to check if a Float value is NaN
predicate IsNaN(f: Float)
{
    f.NaN?
}

// Predicate to check if a Float value is not NaN
predicate IsNotNaN(f: Float)
{
    f.Real?
}

// Comparison for Float values, treating NaN specially
predicate FloatLE(a: Float, b: Float)
    requires IsNotNaN(a) && IsNotNaN(b)
{
    a.value <= b.value
}

// Method to compute nanmin - minimum value ignoring NaN elements
// </vc-preamble>

// <vc-helpers>
// Helper predicate to check if all elements in array are NaN
predicate AllNaN(a: array<Float>)
    reads a
{
    forall i :: 0 <= i < a.Length ==> IsNaN(a[i])
}

// Helper predicate to check if there exists a non-NaN element
predicate ExistsNonNaN(a: array<Float>)
    reads a
{
    exists i :: 0 <= i < a.Length && IsNotNaN(a[i])
}

// Helper predicate to check if a value is minimum among non-NaN elements
predicate IsMinNonNaN(a: array<Float>, val: Float, idx: int)
    reads a
    requires 0 <= idx < a.Length
    requires IsNotNaN(val)
{
    a[idx] == val &&
    IsNotNaN(a[idx]) &&
    (forall j :: 0 <= j < a.Length && IsNotNaN(a[j]) ==> FloatLE(val, a[j]))
}
// </vc-helpers>

// <vc-spec>
method nanmin(a: array<Float>) returns (result: Float)
    requires a.Length >= 1  // Non-empty array constraint
    ensures 
        // Key implication: If there exists at least one non-NaN element, result is not NaN
        (exists i :: 0 <= i < a.Length && IsNotNaN(a[i])) ==> IsNotNaN(result)
    ensures
        // Case 1: If all elements are NaN, result is NaN  
        (forall i :: 0 <= i < a.Length ==> IsNaN(a[i])) ==> IsNaN(result)
    ensures
        // Case 2: If result is not NaN, it's min of non-NaN elements
        IsNotNaN(result) ==> 
            (exists idx :: 0 <= idx < a.Length &&
                result == a[idx] &&
                IsNotNaN(a[idx]) &&
                (forall j :: 0 <= j < a.Length && IsNotNaN(a[j]) ==> FloatLE(result, a[j])))
    ensures
        // Sanity check: result is either NaN or exists in the array
        IsNaN(result) || (exists idx :: 0 <= idx < a.Length && result == a[idx])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed bounds checking in loop invariants */
  if AllNaN(a) {
    result := NaN;
    return;
  }
  
  // Find first non-NaN element
  var i := 0;
  while i < a.Length && IsNaN(a[i])
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> IsNaN(a[k])
  {
    i := i + 1;
  }
  
  // i now points to first non-NaN element
  result := a[i];
  var minIdx := i;
  i := i + 1;
  
  // Find minimum among remaining non-NaN elements
  while i < a.Length
    invariant 0 <= minIdx < a.Length && IsNotNaN(result)
    invariant result == a[minIdx]
    invariant i <= a.Length
    invariant forall k :: 0 <= k < i && k < a.Length && IsNotNaN(a[k]) ==> FloatLE(result, a[k])
  {
    if IsNotNaN(a[i]) && FloatLE(a[i], result) {
      result := a[i];
      minIdx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
