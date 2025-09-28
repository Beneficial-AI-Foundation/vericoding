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
method minNonNan(a: FloatValue, b: FloatValue) returns (r: FloatValue)
  requires !IsNaN(a) && !IsNaN(b)
  ensures !IsNaN(r) && GetValue(r) == if GetValue(a) <= GetValue(b) then GetValue(a) else GetValue(b)
  ensures r == if GetValue(a) <= GetValue(b) then a else b
{
  /* helper modified by LLM (iteration 2): converted function to method to resolve naming conflicts in postcondition */
  r := if GetValue(a) <= GetValue(b) then a else b;
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
  /* code modified by LLM (iteration 2): updated to call the method minNonNan */
  var res: seq<FloatValue> := [];
  var i: int := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==>
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        !IsNaN(res[j]) && GetValue(res[j]) == if GetValue(x[j]) <= GetValue(y[j]) then GetValue(x[j]) else GetValue(y[j])) &&
      (IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        res[j] == y[j]) &&
      (!IsNaN(x[j]) && IsNaN(y[j]) ==> 
        res[j] == x[j]) &&
      (IsNaN(x[j]) && IsNaN(y[j]) ==> 
        IsNaN(res[j])) &&
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        GetValue(res[j]) <= GetValue(x[j]) && GetValue(res[j]) <= GetValue(y[j])) &&
      (!IsNaN(res[j]) ==> 
        (res[j] == x[j] || res[j] == y[j]))
  {
    var minVal: FloatValue;
    if IsNaN(x[i]) && IsNaN(y[i]) {
      minVal := NaN;
    } else if IsNaN(x[i]) {
      minVal := y[i];
    } else if IsNaN(y[i]) {
      minVal := x[i];
    } else {
      minVal := minNonNan(x[i], y[i]);
    }
    res := res + [minVal];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
