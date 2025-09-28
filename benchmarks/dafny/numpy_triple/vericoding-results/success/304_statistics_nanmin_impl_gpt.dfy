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
/* helper modified by LLM (iteration 2): prove transitivity x < y <= z => x <= z */
lemma LtLe_Le(x: real, y: real, z: real)
    requires x < y
    requires y <= z
    ensures x <= z
{
  calc {
    x;
    < y;
    <= z;
  }
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
/* code modified by LLM (iteration 2): fixed quantified assert syntax and maintained invariants across iterations */
{
  var i := 0;
  var found := false;
  var min: Float := NaN;
  var idxMin := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !found ==> (forall j :: 0 <= j < i ==> IsNaN(a[j]))
    invariant found ==> 0 <= idxMin < i
    invariant found ==> min == a[idxMin]
    invariant found ==> IsNotNaN(min)
    invariant found ==> (forall j :: 0 <= j < i && IsNotNaN(a[j]) ==> min.value <= a[j].value)
  {
    var current := a[i];
    if IsNotNaN(current) {
      if !found {
        found := true;
        min := current;
        idxMin := i;
      } else {
        if current.value < min.value {
          assert forall j :: 0 <= j < i && IsNotNaN(a[j]) ==> current.value <= a[j].value by {
            forall j | 0 <= j < i && IsNotNaN(a[j])
              ensures current.value <= a[j].value
            {
              assert min.value <= a[j].value;
              LtLe_Le(current.value, min.value, a[j].value);
            }
          }
          min := current;
          idxMin := i;
        } else {
          assert min.value <= current.value;
        }
      }
    }
    i := i + 1;
  }
  if found {
    result := min;
  } else {
    result := NaN;
  }
}
// </vc-code>
