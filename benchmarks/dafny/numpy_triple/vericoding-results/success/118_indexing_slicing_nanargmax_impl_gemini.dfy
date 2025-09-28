// <vc-preamble>
// Datatype to represent floating point values that can be NaN
datatype FloatValue = Finite(value: real) | NaN

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
  f.NaN?
}

// Predicate to check if a FloatValue is finite (not NaN)
predicate IsFinite(f: FloatValue) {
  f.Finite?
}

// Function to extract the real value from a finite FloatValue
function GetValue(f: FloatValue): real
  requires IsFinite(f)
{
  f.value
}

// Method that returns the index of the maximum non-NaN value in the sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [no change, original is correct] */
method FindFirstFinite(a: seq<FloatValue>) returns (i: nat)
  requires |a| > 0
  requires exists i :: 0 <= i < |a| && IsFinite(a[i])
  ensures 0 <= i < |a|
  ensures IsFinite(a[i])
  ensures forall k :: 0 <= k < i ==> IsNaN(a[k])
{
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> IsNaN(a[k])
    decreases |a| - i
  {
    if IsFinite(a[i]) {
      return;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method nanargmax(a: seq<FloatValue>) returns (idx: nat)
  requires |a| > 0
  // Precondition: at least one element must not be NaN
  requires exists i :: 0 <= i < |a| && IsFinite(a[i])
  // The returned index is valid
  ensures 0 <= idx < |a|
  // The element at the returned index is not NaN
  ensures IsFinite(a[idx])
  // The element at the returned index is greater than or equal to all other non-NaN elements
  ensures forall j :: 0 <= j < |a| && IsFinite(a[j]) ==> GetValue(a[j]) <= GetValue(a[idx])
  // Among elements with the same maximum value, the returned index is the smallest
  ensures forall j :: 0 <= j < |a| && IsFinite(a[j]) && GetValue(a[j]) == GetValue(a[idx]) ==> idx <= j
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [added invariants to fix index-out-of-range errors] */
  var first_finite_idx := FindFirstFinite(a);
  idx := first_finite_idx;

  var j := first_finite_idx + 1;
  while j < |a|
    decreases |a| - j
    invariant j <= |a|
    invariant 0 <= idx < |a|
    invariant 0 <= idx < j
    invariant IsFinite(a[idx])
    invariant forall k :: 0 <= k < j && IsFinite(a[k]) ==> GetValue(a[k]) <= GetValue(a[idx])
    invariant forall k :: 0 <= k < j && IsFinite(a[k]) && GetValue(a[k]) == GetValue(a[idx]) ==> idx <= k
  {
    if IsFinite(a[j]) {
      if GetValue(a[j]) > GetValue(a[idx]) {
        idx := j;
      }
    }
    j := j + 1;
  }
}
// </vc-code>
