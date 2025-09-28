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
// Helper function to check if there exists a finite element at or after index i
predicate ExistsFiniteFrom(a: seq<FloatValue>, i: nat)
  requires i <= |a|
{
  exists k :: i <= k < |a| && IsFinite(a[k])
}

// Helper function to find the first finite element starting from index i
function FindFirstFinite(a: seq<FloatValue>, i: nat): nat
  requires i < |a|
  requires ExistsFiniteFrom(a, i)
  ensures FindFirstFinite(a, i) >= i
  ensures FindFirstFinite(a, i) < |a|
  ensures IsFinite(a[FindFirstFinite(a, i)])
  ensures forall k :: i <= k < FindFirstFinite(a, i) ==> IsNaN(a[k])
  decreases |a| - i
{
  if IsFinite(a[i]) then i
  else FindFirstFinite(a, i + 1)
}

// Helper predicate to check if an index is a valid argmax candidate
predicate IsArgmaxCandidate(a: seq<FloatValue>, idx: nat)
  requires 0 <= idx < |a|
{
  IsFinite(a[idx]) &&
  (forall j :: 0 <= j < |a| && IsFinite(a[j]) ==> GetValue(a[j]) <= GetValue(a[idx])) &&
  (forall j :: 0 <= j < |a| && IsFinite(a[j]) && GetValue(a[j]) == GetValue(a[idx]) ==> idx <= j)
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
  // Find first finite element as starting point
  idx := FindFirstFinite(a, 0);
  
  // Scan through the rest of the array
  var i := idx + 1;
  while i < |a|
    invariant idx < i <= |a|
    invariant 0 <= idx < |a|
    invariant IsFinite(a[idx])
    invariant forall j :: 0 <= j < i && IsFinite(a[j]) ==> GetValue(a[j]) <= GetValue(a[idx])
    invariant forall j :: 0 <= j < i && IsFinite(a[j]) && GetValue(a[j]) == GetValue(a[idx]) ==> idx <= j
  {
    if IsFinite(a[i]) {
      if GetValue(a[i]) > GetValue(a[idx]) {
        idx := i;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
