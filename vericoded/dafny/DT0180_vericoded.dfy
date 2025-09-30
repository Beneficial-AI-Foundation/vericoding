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
  var i := 0;
  idx := 0;
  
  // Find first non-NaN element
  while i < |a| && IsNaN(a[i])
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> IsNaN(a[k])
  {
    i := i + 1;
  }
  
  idx := i;
  var maxVal := GetValue(a[idx]);
  i := i + 1;
  
  // Find maximum among remaining elements
  while i < |a|
    invariant idx < i <= |a|
    invariant 0 <= idx < |a|
    invariant IsFinite(a[idx])
    invariant maxVal == GetValue(a[idx])
    invariant forall j :: 0 <= j < i && IsFinite(a[j]) ==> GetValue(a[j]) <= maxVal
    invariant forall j :: 0 <= j < i && IsFinite(a[j]) && GetValue(a[j]) == maxVal ==> idx <= j
  {
    if IsFinite(a[i]) {
      if GetValue(a[i]) > maxVal {
        idx := i;
        maxVal := GetValue(a[i]);
      }
    }
    i := i + 1;
  }
}
// </vc-code>
