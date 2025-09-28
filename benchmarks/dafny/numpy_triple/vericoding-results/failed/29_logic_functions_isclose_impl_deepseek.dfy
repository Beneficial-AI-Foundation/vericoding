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

  /* helper modified by LLM (iteration 5): Complete helper predicates for all postcondition cases */
  predicate AreFiniteAndWithinTolerance(a_val: Float, b_val: Float, rtol: Float, atol: Float)
    requires FloatLessEqual(rtol, rtol) && FloatLessEqual(atol, atol)
  {
    IsFinite(a_val) && IsFinite(b_val) &&
    FloatLessEqual(FloatAbs(FloatSub(a_val, b_val)), 
                   FloatAdd(atol, FloatMul(rtol, FloatAbs(b_val))))
  }

  predicate AreBothNaN(a_val: Float, b_val: Float, equal_nan: bool): bool
  {
    IsNaN(a_val) && IsNaN(b_val) && equal_nan
  }

  predicate EitherInfiniteEqual(a_val: Float, b_val: Float)
  {
    (!IsFinite(a_val) || !IsFinite(b_val)) && FloatEqual(a_val, b_val)
  }

  function ShouldBeFalse(a_val: Float, b_val: Float, rtol: Float, atol: Float, equal_nan: bool): bool
  {
    (IsFinite(a_val) && IsFinite(b_val) && 
     FloatGreater(FloatAbs(FloatSub(a_val, b_val)), 
                  FloatAdd(atol, FloatMul(rtol, FloatAbs(b_val))))) ||
    ((!IsFinite(a_val) || !IsFinite(b_val)) && 
     !FloatEqual(a_val, b_val)) ||
    (IsNaN(a_val) && IsNaN(b_val) && !equal_nan)
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
  /* code modified by LLM (iteration 5): Complete loop invariants matching all postconditions */
  var res_elements: seq<bool> := [];
  var i: nat := 0;
  
  while i < a.length
    invariant |res_elements| == i
    invariant i <= a.length
    invariant forall j :: 0 <= j < i ==> (
      // Core tolerance check for finite values
      (IsFinite(a.Get(j)) && IsFinite(b.Get(j))) ==> (
        res_elements[j] <==> 
        FloatLessEqual(FloatAbs(FloatSub(a.Get(j), b.Get(j))), 
                       FloatAdd(atol, FloatMul(rtol, FloatAbs(b.Get(j)))))
      )
    )
    invariant forall j :: 0 <= j < i ==> (
      // Infinite values are equal if they match exactly
      (!IsFinite(a.Get(j)) || !IsFinite(b.Get(j))) ==> (
        res_elements[j] <==> FloatEqual(a.Get(j), b.Get(j))
      )
    )
    invariant forall j :: 0 <= j < i ==> (
      // NaN handling depends on equal_nan parameter
      (IsNaN(a.Get(j)) && IsNaN(b.Get(j))) ==> (
        res_elements[j] <==> equal_nan
      )
    )
    invariant forall j :: 0 <= j < i ==> (
      // Completeness: result is false in specific cases
      !res_elements[j] <==> (
        (IsFinite(a.Get(j)) && IsFinite(b.Get(j)) && 
         FloatGreater(FloatAbs(FloatSub(a.Get(j), b.Get(j))), 
                      FloatAdd(atol, FloatMul(rtol, FloatAbs(b.Get(j)))))) ||
        ((!IsFinite(a.Get(j)) || !IsFinite(b.Get(j))) && 
         !FloatEqual(a.Get(j), b.Get(j))) ||
        (IsNaN(a.Get(j)) && IsNaN(b.Get(j)) && !equal_nan)
      )
    )
  {
    var a_val: Float := a.Get(i);
    var b_val: Float := b.Get(i);
    
    var close: bool;
    
    if IsNaN(a_val) && IsNaN(b_val) {
      close := equal_nan;
    } else if !IsFinite(a_val) || !IsFinite(b_val) {
      close := FloatEqual(a_val, b_val);
    } else {
      close := FloatLessEqual(FloatAbs(FloatSub(a_val, b_val)), 
                             FloatAdd(atol, FloatMul(rtol, FloatAbs(b_val))));
    }
    
    res_elements := res_elements + [close];
    i := i + 1;
  }
  
  result := Vector(res_elements, a.length);
}
// </vc-code>
