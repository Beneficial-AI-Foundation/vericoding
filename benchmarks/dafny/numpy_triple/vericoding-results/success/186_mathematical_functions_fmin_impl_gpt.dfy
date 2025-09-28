// <vc-preamble>
// Represents a floating point value that can be NaN
datatype FloatValue = Value(val: real) | NaN

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
  f.NaN?
}

// Get the real value from a non-NaN FloatValue
function GetValue(f: FloatValue): real
  requires !IsNaN(f)
{
  f.val
}

// Element-wise minimum of two vectors with NaN handling
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): reformatted ensures with parentheses to avoid indentation warning and kept semantics */
function FMinElem(a: FloatValue, b: FloatValue): FloatValue
  ensures (IsNaN(a) && IsNaN(b)) ==> IsNaN(FMinElem(a, b))
  ensures (IsNaN(a) && !IsNaN(b)) ==> FMinElem(a, b) == b
  ensures (!IsNaN(a) && IsNaN(b)) ==> FMinElem(a, b) == a
  ensures (!IsNaN(a) && !IsNaN(b)) ==>
           (!IsNaN(FMinElem(a, b)) &&
            GetValue(FMinElem(a, b)) == (if GetValue(a) <= GetValue(b) then GetValue(a) else GetValue(b)))
  ensures (!IsNaN(a) && !IsNaN(b)) ==>
           (GetValue(FMinElem(a, b)) <= GetValue(a) && GetValue(FMinElem(a, b)) <= GetValue(b))
  ensures !IsNaN(FMinElem(a, b)) ==> (FMinElem(a, b) == a || FMinElem(a, b) == b)
{
  if IsNaN(a) then
    if IsNaN(b) then NaN else b
  else if IsNaN(b) then a
  else if GetValue(a) <= GetValue(b) then a else b
}
// </vc-helpers>

// <vc-spec>
method fmin(x: seq<FloatValue>, y: seq<FloatValue>) returns (result: seq<FloatValue>)
  requires |x| == |y|
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |result| ==>
    // NaN handling cases
    (!IsNaN(x[i]) && !IsNaN(y[i]) ==> 
      !IsNaN(result[i]) && GetValue(result[i]) == if GetValue(x[i]) <= GetValue(y[i]) then GetValue(x[i]) else GetValue(y[i])) &&
    (IsNaN(x[i]) && !IsNaN(y[i]) ==> 
      result[i] == y[i]) &&
    (!IsNaN(x[i]) && IsNaN(y[i]) ==> 
      result[i] == x[i]) &&
    (IsNaN(x[i]) && IsNaN(y[i]) ==> 
      IsNaN(result[i])) &&
    // Mathematical properties
    (!IsNaN(x[i]) && !IsNaN(y[i]) ==> 
      GetValue(result[i]) <= GetValue(x[i]) && GetValue(result[i]) <= GetValue(y[i])) &&
    (!IsNaN(result[i]) ==> 
      (result[i] == x[i] || result[i] == y[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build result via loop using FMinElem and preserve correspondence with inputs */
  var r: seq<FloatValue> := [];
  var i: int := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |r| == i
    invariant |x| == |y|
    invariant forall j :: 0 <= j < i ==> r[j] == FMinElem(x[j], y[j])
  {
    r := r + [FMinElem(x[i], y[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
