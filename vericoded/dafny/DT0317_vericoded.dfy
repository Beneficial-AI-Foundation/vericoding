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
function MinFloat(a: FloatValue, b: FloatValue): FloatValue
{
  if IsNaN(a) && IsNaN(b) then
    NaN
  else if IsNaN(a) then
    b
  else if IsNaN(b) then
    a
  else if GetValue(a) <= GetValue(b) then
    a
  else
    b
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
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        !IsNaN(result[j]) && GetValue(result[j]) == if GetValue(x[j]) <= GetValue(y[j]) then GetValue(x[j]) else GetValue(y[j])) &&
      (IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        result[j] == y[j]) &&
      (!IsNaN(x[j]) && IsNaN(y[j]) ==> 
        result[j] == x[j]) &&
      (IsNaN(x[j]) && IsNaN(y[j]) ==> 
        IsNaN(result[j])) &&
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        GetValue(result[j]) <= GetValue(x[j]) && GetValue(result[j]) <= GetValue(y[j])) &&
      (!IsNaN(result[j]) ==> 
        (result[j] == x[j] || result[j] == y[j]))
  {
    result := result + [MinFloat(x[i], y[i])];
    i := i + 1;
  }
}
// </vc-code>
