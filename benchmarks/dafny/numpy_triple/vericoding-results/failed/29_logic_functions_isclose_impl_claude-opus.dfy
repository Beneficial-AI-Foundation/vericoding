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
  /* code modified by LLM (iteration 5): fixed case handling to properly maintain loop invariants for NaN, finite, and infinite values */
  var resultSeq: seq<bool> := [];
  var i := 0;
  
  while i < a.length
    invariant 0 <= i <= a.length
    invariant |resultSeq| == i
    invariant forall j :: 0 <= j < i ==> (
      (IsFinite(a.Get(j)) && IsFinite(b.Get(j))) ==> (
        resultSeq[j] <==> 
        FloatLessEqual(FloatAbs(FloatSub(a.Get(j), b.Get(j))), 
                       FloatAdd(atol, FloatMul(rtol, FloatAbs(b.Get(j)))))
      )
    )
    invariant forall j :: 0 <= j < i ==> (
      (!IsFinite(a.Get(j)) || !IsFinite(b.Get(j))) ==> (
        resultSeq[j] <==> FloatEqual(a.Get(j), b.Get(j))
      )
    )
    invariant forall j :: 0 <= j < i ==> (
      (IsNaN(a.Get(j)) && IsNaN(b.Get(j))) ==> (
        resultSeq[j] <==> equal_nan
      )
    )
    invariant forall j :: 0 <= j < i ==> (
      !resultSeq[j] <==> (
        (IsFinite(a.Get(j)) && IsFinite(b.Get(j)) && 
         FloatGreater(FloatAbs(FloatSub(a.Get(j), b.Get(j))), 
                      FloatAdd(atol, FloatMul(rtol, FloatAbs(b.Get(j)))))) ||
        ((!IsFinite(a.Get(j)) || !IsFinite(b.Get(j))) && 
         !FloatEqual(a.Get(j), b.Get(j))) ||
        (IsNaN(a.Get(j)) && IsNaN(b.Get(j)) && !equal_nan)
      )
    )
  {
    var aVal := a.Get(i);
    var bVal := b.Get(i);
    var isCloseVal: bool;
    
    if IsNaN(aVal) && IsNaN(bVal) {
      // Both are NaN - use equal_nan flag
      isCloseVal := equal_nan;
    } else if IsNaN(aVal) || IsNaN(bVal) {
      // Only one is NaN - always false
      isCloseVal := false;
    } else if IsFinite(aVal) && IsFinite(bVal) {
      // Both are finite - use tolerance check
      var diff := FloatAbs(FloatSub(aVal, bVal));
      var tolerance := FloatAdd(atol, FloatMul(rtol, FloatAbs(bVal)));
      isCloseVal := FloatLessEqual(diff, tolerance);
    } else {
      // At least one is infinite (but not NaN) - check exact equality
      isCloseVal := FloatEqual(aVal, bVal);
    }
    
    resultSeq := resultSeq + [isCloseVal];
    i := i + 1;
  }
  
  result := Vector(resultSeq, a.length);
}
// </vc-code>
