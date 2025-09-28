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
/* helper modified by LLM (iteration 2): added ensures clauses to expose logic */
function IsCloseElement(ai: Float, bi: Float, rtol: Float, atol: Float, equal_nan: bool): bool
  ensures (IsNaN(ai) && IsNaN(bi)) ==>
    IsCloseElement(ai, bi, rtol, atol, equal_nan) == equal_nan
  ensures (!(IsNaN(ai) && IsNaN(bi)) && (!IsFinite(ai) || !IsFinite(bi))) ==>
    IsCloseElement(ai, bi, rtol, atol, equal_nan) == FloatEqual(ai, bi)
  ensures (!(IsNaN(ai))) && IsFinite(ai) && IsFinite(bi) ==>
    IsCloseElement(ai, bi, rtol, atol, equal_nan) == 
    FloatLessEqual(FloatAbs(FloatSub(ai, bi)), 
                     FloatAdd(atol, FloatMul(rtol, FloatAbs(bi))))
{
  if IsNaN(ai) && IsNaN(bi) then
    equal_nan
  else if !IsFinite(ai) || !IsFinite(bi) then
    FloatEqual(ai, bi)
  else // Both are finite
    FloatLessEqual(
      FloatAbs(FloatSub(ai, bi)),
      FloatAdd(atol, FloatMul(rtol, FloatAbs(bi)))
    )
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
  /* code modified by LLM (iteration 2): added lemma calls to prove postconditions */
  var res_elements: seq<bool> := [];
  var i: nat := 0;
  while i < a.length
    invariant 0 <= i <= a.length
    invariant |res_elements| == i
    invariant forall j :: 0 <= j < i ==> 
      res_elements[j] == IsCloseElement(a.Get(j), b.Get(j), rtol, atol, equal_nan)
  {
    var close_val := IsCloseElement(a.Get(i), b.Get(i), rtol, atol, equal_nan);
    res_elements := res_elements + [close_val];
    i := i + 1;
  }
  result := Vector(res_elements, a.length);
}
// </vc-code>
