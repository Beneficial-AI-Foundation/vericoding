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
/* helper modified by LLM (iteration 2): simple lemma that real implies not NaN */
lemma RealNotNaN(f: Float)
  ensures IsReal(f) ==> !IsNaN(f)
{
  if IsReal(f) {
    assert !IsNaN(f);
  }
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
  /* code modified by LLM (iteration 2): find first real element and then the leftmost minimum among reals */
  var n := a.Length;
  var i := 0;
  // Find first real index
  while i < n && !IsReal(a[i])
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> !IsReal(a[j])
    invariant exists j :: i <= j < n && IsReal(a[j])
  {
    i := i + 1;
  }
  assert i < n;
  assert IsReal(a[i]);

  var cur := i;
  var k := i + 1;
  while k < n
    invariant 0 <= k <= n
    invariant 0 <= cur < n
    invariant IsReal(a[cur])
    invariant forall j :: 0 <= j < k && IsReal(a[j]) ==> FloatLessOrEqual(a[cur], a[j])
    invariant forall j :: 0 <= j < cur && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[cur])
  {
    if IsReal(a[k]) {
      if GetReal(a[k]) < GetReal(a[cur]) {
        cur := k;
      }
    }
    k := k + 1;
  }

  idx := cur;
}

// </vc-code>
