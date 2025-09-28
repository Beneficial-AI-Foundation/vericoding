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
lemma FloatLE_transitive(a: Float, b: Float, c: Float)
  requires IsNotNaN(a) && IsNotNaN(b) && IsNotNaN(c)
  requires FloatLE(a,b) && FloatLE(b,c)
  ensures FloatLE(a,c)
{
  assert a.value <= b.value;
  assert b.value <= c.value;
  assert a.value <= c.value;
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
  var n := a.Length;
  var i := 0;
  var found := false;
  var idx := 0;
  var cur := NaN;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant (exists k :: 0 <= k < i && IsNotNaN(a[k])) ==> found
    invariant found ==> 0 <= idx < i && cur == a[idx] && IsNotNaN(cur) && (forall j :: 0 <= j < i && IsNotNaN(a[j]) ==> FloatLE(cur, a[j]))
  {
    if !found {
      if IsNotNaN(a[i]) {
        found := true;
        idx := i;
        cur := a[i];
      }
    } else {
      if IsNotNaN(a[i]) {
        if FloatLE(a[i], cur) {
          cur := a[i];
          idx := i;
        }
      }
    }
    i := i + 1;
  }
  if found {
    result := cur;
  } else {
    result := NaN;
  }
}

// </vc-code>
