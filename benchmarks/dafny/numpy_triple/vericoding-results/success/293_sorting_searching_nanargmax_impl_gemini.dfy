// <vc-preamble>
// Datatype to represent floating point values that can be NaN
datatype FloatValue = NaN | Value(val: real)

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Predicate to check if a FloatValue is not NaN
predicate IsNotNaN(f: FloatValue) {
    f.Value?
}

// Function to compare two non-NaN FloatValues
predicate LessOrEqual(f1: FloatValue, f2: FloatValue)
    requires IsNotNaN(f1) && IsNotNaN(f2)
{
    f1.val <= f2.val
}

// Function to check equality of two non-NaN FloatValues
predicate Equal(f1: FloatValue, f2: FloatValue)
    requires IsNotNaN(f1) && IsNotNaN(f2)
{
    f1.val == f2.val
}

// Predicate to check if at least one element in the array is not NaN
predicate HasNonNaN(a: seq<FloatValue>) {
    exists i :: 0 <= i < |a| && IsNotNaN(a[i])
}

/**
 * Returns the index of the maximum non-NaN value in the array.
 * In case of ties, returns the index of the first occurrence.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no logical changes needed */
method FindFirstNonNaNIndex(a: seq<FloatValue>) returns (k: nat)
    requires |a| > 0
    requires HasNonNaN(a)
    ensures 0 <= k < |a|
    ensures IsNotNaN(a[k])
    ensures forall i :: 0 <= i < k ==> IsNaN(a[i])
{
    k := 0;
    while k < |a| && IsNaN(a[k])
        invariant 0 <= k <= |a|
        invariant forall i :: 0 <= i < k ==> IsNaN(a[i])
    {
        k := k + 1;
    }
    assert k < |a|;
}
// </vc-helpers>

// <vc-spec>
method nanargmax(a: seq<FloatValue>) returns (idx: nat)
    // Preconditions: array is non-empty and contains at least one non-NaN value
    requires |a| > 0
    requires HasNonNaN(a)
    
    // Postconditions
    ensures 0 <= idx < |a|
    ensures IsNotNaN(a[idx])
    ensures forall j :: 0 <= j < |a| && IsNotNaN(a[j]) ==> LessOrEqual(a[j], a[idx])
    ensures forall j :: 0 <= j < |a| && IsNotNaN(a[j]) && Equal(a[j], a[idx]) ==> idx <= j
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added stronger invariant to help verifier with index relations */
  var k := FindFirstNonNaNIndex(a);

  idx := k;
  var i := k + 1;
  while i < |a|
    invariant k + 1 <= i <= |a|
    invariant 0 <= idx < i
    invariant forall j :: 0 <= j < k ==> IsNaN(a[j])
    invariant IsNotNaN(a[idx])
    invariant forall j :: 0 <= j < i && IsNotNaN(a[j]) ==> LessOrEqual(a[j], a[idx])
    invariant forall j :: 0 <= j < i && IsNotNaN(a[j]) && Equal(a[j], a[idx]) ==> idx <= j
  {
    if a[i].Value? {
      if a[idx].val < a[i].val {
        idx := i;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
