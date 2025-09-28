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
function IsElementClose(a: Float, b: Float, rtol: Float, atol: Float, equal_nan: bool): bool
{
  if IsNaN(a) || IsNaN(b) then
    if IsNaN(a) && IsNaN(b) then
      equal_nan
    else
      false
    else
    if IsFinite(a) && IsFinite(b) then
      FloatLessEqual(FloatAbs(FloatSub(a, b)), FloatAdd(atol, FloatMul(rtol, FloatAbs(b))))
    else
      FloatEqual(a, b)
}
/* helper modified by LLM (iteration 4): fixed syntax by adding 'then' to if expressions */
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
  /* code modified by LLM (iteration 4): implemented element-wise closeness comparison using loop with invariants */
  var resultElements: seq<bool> := [];
  var i: int := 0;
  while i < a.length
    invariant 0 <= i <= a.length
    invariant |resultElements| == i
    invariant forall j :: 0 <= j < i ==> resultElements[j] <==> IsElementClose(a.Get(j), b.Get(j), rtol, atol, equal_nan)
  {
    var aElement := a.Get(i);
    var bElement := b.Get(i);
    var isClose := IsElementClose(aElement, bElement, rtol, atol, equal_nan);
    resultElements := resultElements + [isClose];
    i := i + 1;
  }
  result := Vector(resultElements, a.length);
}
// </vc-code>
