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
  while i < a.Length && IsNaN(a[i])
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> IsNaN(a[j])
  {
    i := i + 1;
  }
  
  idx := i;
  i := i + 1;
  
  while i < a.Length
    invariant idx < i <= a.Length
    invariant 0 <= idx < a.Length
    invariant IsReal(a[idx])
    invariant forall j :: 0 <= j < i && IsReal(a[j]) ==> FloatLessOrEqual(a[idx], a[j])
    invariant forall j :: 0 <= j < idx && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[idx])
  {
    if IsReal(a[i]) && GetReal(a[i]) < GetReal(a[idx]) {
      idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
