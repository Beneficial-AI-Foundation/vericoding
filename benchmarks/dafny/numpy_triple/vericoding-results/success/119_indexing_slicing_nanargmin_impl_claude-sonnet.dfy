// <vc-preamble>
// Custom datatype to represent floating point values that can be NaN
datatype Float = NaN | Real(value: real)

// Predicate to check if a Float is NaN
predicate IsNaN(f: Float)
{
    f.NaN?
}

// Predicate to check if a Float is not NaN
predicate IsReal(f: Float)
{
    f.Real?
}

// Function to extract real value (only valid for Real values)
function GetReal(f: Float): real
  requires IsReal(f)
{
  f.value
}

// Comparison function for Float values (NaN is not comparable)
predicate FloatLessOrEqual(x: Float, y: Float)
  requires IsReal(x) && IsReal(y)
{
  GetReal(x) <= GetReal(y)
}

// Method that returns the index of the minimum value ignoring NaN values
// </vc-preamble>

// <vc-helpers>
predicate HasRealAt(a: array<Float>, i: int)
  reads a
{
  0 <= i < a.Length && IsReal(a[i])
}

/* helper modified by LLM (iteration 3): added lemma to prove the found element is minimal */
lemma EstablishMinimumProperty(a: array<Float>, idx: int, old_idx: int)
  requires 0 <= old_idx < a.Length
  requires IsReal(a[old_idx])
  requires 0 <= idx < a.Length
  requires IsReal(a[idx])
  requires GetReal(a[idx]) < GetReal(a[old_idx])
  requires forall j :: 0 <= j < old_idx && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[old_idx])
  ensures forall j :: 0 <= j < old_idx && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[idx])
{
  // Since all elements before old_idx are > a[old_idx] and a[idx] < a[old_idx],
  // all elements before old_idx are > a[idx]
}
// </vc-helpers>

// <vc-spec>
method nanargmin(a: array<Float>) returns (idx: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsReal(a[i])
  ensures 0 <= idx < a.Length
  ensures IsReal(a[idx])
  ensures forall j :: 0 <= j < a.Length && IsReal(a[j]) ==> FloatLessOrEqual(a[idx], a[j])
  ensures forall j :: 0 <= j < idx && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[idx])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): track previous minimum to maintain postcondition */
  idx := 0;
  
  // Find first real element
  while idx < a.Length && IsNaN(a[idx])
    invariant 0 <= idx <= a.Length
    invariant forall k :: 0 <= k < idx ==> IsNaN(a[k])
    decreases a.Length - idx
  {
    idx := idx + 1;
  }
  
  // Search for minimum among remaining elements
  var i := idx + 1;
  while i < a.Length
    invariant 0 <= idx < a.Length
    invariant IsReal(a[idx])
    invariant idx < i <= a.Length
    invariant forall j :: 0 <= j < i && IsReal(a[j]) ==> FloatLessOrEqual(a[idx], a[j])
    invariant forall j :: 0 <= j < idx && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[idx])
  {
    if IsReal(a[i]) {
      if FloatLessOrEqual(a[i], a[idx]) {
        if GetReal(a[i]) < GetReal(a[idx]) {
          var old_idx := idx;
          EstablishMinimumProperty(a, i, old_idx);
          idx := i;
        }
      }
    }
    i := i + 1;
  }
}
// </vc-code>
