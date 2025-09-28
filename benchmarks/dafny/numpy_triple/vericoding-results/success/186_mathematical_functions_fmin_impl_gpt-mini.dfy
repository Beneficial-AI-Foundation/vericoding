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
function MinElem(xi: FloatValue, yi: FloatValue): FloatValue
{
  if IsNaN(xi) && IsNaN(yi) then FloatValue.NaN
  else if IsNaN(xi) then yi
  else if IsNaN(yi) then xi
  else if GetValue(xi) <= GetValue(yi) then xi else yi
}

lemma MinElemProperties(xi: FloatValue, yi: FloatValue)
  ensures (!IsNaN(xi) && !IsNaN(yi) ==> 
    !IsNaN(MinElem(xi, yi)) && GetValue(MinElem(xi, yi)) == (if GetValue(xi) <= GetValue(yi) then GetValue(xi) else GetValue(yi)))
  ensures (IsNaN(xi) && !IsNaN(yi) ==> MinElem(xi, yi) == yi)
  ensures (!IsNaN(xi) && IsNaN(yi) ==> MinElem(xi, yi) == xi)
  ensures (IsNaN(xi) && IsNaN(yi) ==> IsNaN(MinElem(xi, yi)))
  ensures (!IsNaN(xi) && !IsNaN(yi) ==> GetValue(MinElem(xi, yi)) <= GetValue(xi) && GetValue(MinElem(xi, yi)) <= GetValue(yi))
  ensures (!IsNaN(MinElem(xi, yi)) ==> (MinElem(xi, yi) == xi || MinElem(xi, yi) == yi))
{
  if IsNaN(xi) && IsNaN(yi) {
    assert MinElem(xi, yi) == FloatValue.NaN;
  } else if IsNaN(xi) {
    assert MinElem(xi, yi) == yi;
  } else if IsNaN(yi) {
    assert MinElem(xi, yi) == xi;
  } else {
    if GetValue(xi) <= GetValue(yi) {
      assert MinElem(xi, yi) == xi;
    } else {
      assert MinElem(xi, yi) == yi;
    }
  }
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
  var n := |x|;
  var res: seq<FloatValue> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==>
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        !IsNaN(res[j]) && GetValue(res[j]) == (if GetValue(x[j]) <= GetValue(y[j]) then GetValue(x[j]) else GetValue(y[j]))) &&
      (IsNaN(x[j]) && !IsNaN(y[j]) ==> res[j] == y[j]) &&
      (!IsNaN(x[j]) && IsNaN(y[j]) ==> res[j] == x[j]) &&
      (IsNaN(x[j]) && IsNaN(y[j]) ==> IsNaN(res[j])) &&
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> GetValue(res[j]) <= GetValue(x[j]) && GetValue(res[j]) <= GetValue(y[j])) &&
      (!IsNaN(res[j]) ==> (res[j] == x[j] || res[j] == y[j]))
  {
    var m := MinElem(x[i], y[i]);
    MinElemProperties(x[i], y[i]);
    res := res + [m];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
