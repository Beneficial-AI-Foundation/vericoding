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
/* helper modified by LLM (iteration 5): No changes needed. */
predicate IsCloseElement(a_val: Float, b_val: Float, rtol: Float, atol: Float, equal_nan: bool) {
  if IsNaN(a_val) && IsNaN(b_val) then
    equal_nan
  else if !IsFinite(a_val) || !IsFinite(b_val) then
    FloatEqual(a_val, b_val)
  else
    FloatLessEqual(FloatAbs(FloatSub(a_val, b_val)), FloatAdd(atol, FloatMul(rtol, FloatAbs(b_val))))
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
/* code modified by LLM (iteration 5): The `result.Valid()` postcondition was failing because `length` field of the vector was not implicitly set as being equal to the sequence length. Explicitly assigning `a.length` as the second argument when creating `Vector` type fixes this. */
{
  var results_seq: seq<bool> := [];

  for i := 0 to a.length - 1
    invariant 0 <= i <= a.length
    invariant |results_seq| == i
    invariant forall j :: 0 <= j < i ==> results_seq[j] == IsCloseElement(a.Get(j), b.Get(j), rtol, atol, equal_nan)
  {
    var a_val := a.Get(i);
    var b_val := b.Get(i);

    var is_close_val: bool;
    if IsNaN(a_val) && IsNaN(b_val) {
      is_close_val := equal_nan;
    } else if !IsFinite(a_val) || !IsFinite(b_val) {
      is_close_val := FloatEqual(a_val, b_val);
    } else {
      is_close_val := FloatLessEqual(FloatAbs(FloatSub(a_val, b_val)), FloatAdd(atol, FloatMul(rtol, FloatAbs(b_val))));
    }
    results_seq := results_seq + [is_close_val];
  }

  result := Vector(results_seq, a.length);
}
// </vc-code>
