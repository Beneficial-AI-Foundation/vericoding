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
  var i := 0;
  result := NaN;
  
  // Find first non-NaN element
  while i < a.Length && IsNaN(a[i])
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> IsNaN(a[j])
  {
    i := i + 1;
  }
  
  if i < a.Length {
    // Found at least one non-NaN element
    result := a[i];
    var j := i + 1;
    
    while j < a.Length
      invariant i <= j <= a.Length
      invariant IsNotNaN(result)
      invariant exists idx :: 0 <= idx < a.Length && result == a[idx] && IsNotNaN(a[idx])
      invariant forall k :: 0 <= k < j && IsNotNaN(a[k]) ==> FloatLE(result, a[k])
    {
      if IsNotNaN(a[j]) && a[j].value < result.value {
        result := a[j];
      }
      j := j + 1;
    }
  }
}
// </vc-code>
