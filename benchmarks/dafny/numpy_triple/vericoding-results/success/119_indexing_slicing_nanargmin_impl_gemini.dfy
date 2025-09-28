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
  var i := 0;
  while i < a.Length && !IsReal(a[i])
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> !IsReal(a[k])
  {
    i := i + 1;
  }
  idx := i;

  var j := idx + 1;
  while j < a.Length
    invariant 0 <= idx < a.Length
    invariant IsReal(a[idx])
    invariant idx < j <= a.Length
    invariant forall k :: 0 <= k < j && IsReal(a[k]) ==> FloatLessOrEqual(a[idx], a[k])
    invariant forall k :: 0 <= k < idx && IsReal(a[k]) ==> GetReal(a[k]) > GetReal(a[idx])
  {
    if IsReal(a[j]) {
      if GetReal(a[j]) < GetReal(a[idx]) {
        idx := j;
      }
    }
    j := j + 1;
  }
}
// </vc-code>
