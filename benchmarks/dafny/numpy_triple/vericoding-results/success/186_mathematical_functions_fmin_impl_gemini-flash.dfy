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
/* helper modified by LLM (iteration 4): No changes needed, helper is correctly defined */
function fmin_scalar(a: FloatValue, b: FloatValue): FloatValue
{
  if IsNaN(a) && IsNaN(b) then NaN
  else if IsNaN(a) then b
  else if IsNaN(b) then a
  else if a.val <= b.val then a
  else b
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
/* code modified by LLM (iteration 4): Fixed compilation errors related to `new Array` and assignment of array to sequence by using `new FloatValue[|x|]` and converting to sequence. */
{
  var i := 0;
  var temp_result_array := new FloatValue[|x|];

  while i < |x|
    invariant 0 <= i <= |x|
    invariant |x| == |y|
    invariant forall k :: 0 <= k < i ==> temp_result_array[k] == fmin_scalar(x[k], y[k])
  {
    temp_result_array[i] := fmin_scalar(x[i], y[i]);
    i := i + 1;
  }
  result := temp_result_array[..];
}
// </vc-code>
