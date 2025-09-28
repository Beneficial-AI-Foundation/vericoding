// <vc-preamble>
// Abstract float type with IEEE 754 properties
type {:extern "double"} Float

// Predicates for float properties
predicate {:extern} IsFinite(f: Float)
predicate {:extern} IsNaN(f: Float)

// Float operations
function {:extern} FloatAbs(f: Float): Float
function {:extern} FloatAdd(a: Float, b: Float): Float
function {:extern} FloatSub(a: Float, b: Float): Float
function {:extern} FloatMul(a: Float, b: Float): Float
function {:extern} FloatLessEqual(a: Float, b: Float): bool
function {:extern} FloatGreater(a: Float, b: Float): bool
function {:extern} FloatEqual(a: Float, b: Float): bool

// Vector type
datatype Vector<T> = Vector(elements: seq<T>, length: nat)
{
  predicate Valid() {
    |elements| == length
  }
  
  function Get(i: nat): T
    requires i < length
    requires Valid()
  {
    elements[i]
  }
}

// Method to perform element-wise closeness comparison
// </vc-preamble>

// <vc-helpers>
function IsCloseElement(a: Float, b: Float, rtol: Float, atol: Float, equal_nan: bool): bool
{
  if IsNaN(a) && IsNaN(b) then
    equal_nan
  else if IsFinite(a) && IsFinite(b) then
    FloatLessEqual(FloatAbs(FloatSub(a, b)), FloatAdd(atol, FloatMul(rtol, FloatAbs(b))))
  else
    FloatEqual(a, b)
}
// </vc-helpers>

// <vc-spec>
method IsClose(a: Vector<Float>, b: Vector<Float>, rtol: Float, atol: Float, equal_nan: bool) 
  returns (result: Vector<bool>)
  requires a.Valid() && b.Valid()
  requires a.length == b.length
  requires FloatLessEqual(rtol, rtol) // rtol >= 0 (placeholder for proper comparison)
  requires FloatLessEqual(atol, atol) // atol >= 0 (placeholder for proper comparison)
  ensures result.Valid()
  ensures result.length == a.length
  ensures forall i :: 0 <= i < a.length ==> (
    // Core tolerance check for finite values
    (IsFinite(a.Get(i)) && IsFinite(b.Get(i))) ==> (
      result.Get(i) <==> 
      FloatLessEqual(FloatAbs(FloatSub(a.Get(i), b.Get(i))), 
                     FloatAdd(atol, FloatMul(rtol, FloatAbs(b.Get(i)))))
    )
  )
  ensures forall i :: 0 <= i < a.length ==> (
    // Infinite values are equal if they match exactly
    (!IsFinite(a.Get(i)) || !IsFinite(b.Get(i))) ==> (
      result.Get(i) <==> FloatEqual(a.Get(i), b.Get(i))
    )
  )
  ensures forall i :: 0 <= i < a.length ==> (
    // NaN handling depends on equal_nan parameter
    (IsNaN(a.Get(i)) && IsNaN(b.Get(i))) ==> (
      result.Get(i) <==> equal_nan
    )
  )
  ensures forall i :: 0 <= i < a.length ==> (
    // Completeness: result is false in specific cases
    !result.Get(i) <==> (
      (IsFinite(a.Get(i)) && IsFinite(b.Get(i)) && 
       FloatGreater(FloatAbs(FloatSub(a.Get(i), b.Get(i))), 
                    FloatAdd(atol, FloatMul(rtol, FloatAbs(b.Get(i)))))) ||
      ((!IsFinite(a.Get(i)) || !IsFinite(b.Get(i))) && 
       !FloatEqual(a.Get(i), b.Get(i))) ||
      (IsNaN(a.Get(i)) && IsNaN(b.Get(i)) && !equal_nan)
    )
  )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed array to sequence conversion */
  var bools := new bool[a.length];
  for i := 0 to a.length
    invariant 0 <= i <= a.length
    invariant forall j :: 0 <= j < i ==> bools[j] == IsCloseElement(a.Get(j), b.Get(j), rtol, atol, equal_nan)
  {
    bools[i] := IsCloseElement(a.Get(i), b.Get(i), rtol, atol, equal_nan);
  }
  result := Vector(bools[..], a.length);
}
// </vc-code>
