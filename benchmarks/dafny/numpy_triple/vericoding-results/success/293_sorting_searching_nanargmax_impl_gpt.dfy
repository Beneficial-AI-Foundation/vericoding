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
lemma LtImpliesLe(x: real, y: real)
  ensures x < y ==> x <= y
{
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
  var best: nat := 0;
  while best < |a| && a[best].NaN?
    invariant 0 <= best <= |a|
    invariant exists k :: best <= k < |a| && a[k].Value?
    invariant forall j :: 0 <= j < best ==> a[j].NaN?
    decreases |a| - best
  {
    best := best + 1;
  }
  assert best < |a|;
  assert a[best].Value?;
  var i: nat := best + 1;
  while i < |a|
    invariant 0 <= best < |a|
    invariant a[best].Value?
    invariant best < i <= |a|
    invariant forall j :: 0 <= j < i && a[j].Value? ==> a[j].val <= a[best].val
    invariant forall j :: 0 <= j < i && a[j].Value? && a[j].val == a[best].val ==> best <= j
    decreases |a| - i
  {
    if a[i].Value? {
      if a[best].val < a[i].val {
        assert forall j :: 0 <= j < i && a[j].Value? ==> a[j].val <= a[i].val;
        best := i;
      }
    }
    i := i + 1;
  }
  idx := best;
}
// </vc-code>
