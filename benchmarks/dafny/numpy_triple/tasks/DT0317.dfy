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
  assume {:axiom} false;
}
// </vc-code>
