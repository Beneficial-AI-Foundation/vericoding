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
function FindMaxIndex(a: seq<FloatValue>, start: nat): (index: nat)
  decreases |a| - start
  requires 0 <= start < |a|
  requires exists i :: start <= i < |a| && IsFinite(a[i])
  ensures start <= index < |a|
  ensures IsFinite(a[index])
  ensures forall j :: start <= j < |a| && IsFinite(a[j]) ==> GetValue(a[j]) <= GetValue(a[index])
  ensures forall j :: start <= j < |a| && IsFinite(a[j]) && GetValue(a[j]) == GetValue(a[index]) ==> index <= j
{
  /* helper modified by LLM (iteration 5): moved decreases clause to correct position */
  if start == |a| - 1 then
    start
  else
    if exists i :: start+1 <= i < |a| && IsFinite(a[i]) then
      var next := FindMaxIndex(a, start+1);
      if IsFinite(a[start]) && GetValue(a[start]) >= GetValue(a[next]) then
        start
      else
        next
    else
      start
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
  /* code modified by LLM (iteration 5): no change needed */
  idx := FindMaxIndex(a, 0);
}
// </vc-code>
