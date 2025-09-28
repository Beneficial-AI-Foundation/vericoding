// <vc-preamble>
// Float datatype that can represent NaN and regular values
datatype Float = NaN | Value(val: real)

// Predicate to check if a Float is NaN
predicate IsNaN(f: Float) {
    f.NaN?
}

// Maximum function for real values
function Max(x: real, y: real): real {
    if x >= y then x else y
}

// Element-wise maximum of two arrays with NaN handling
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fmax(x: array<Float>, y: array<Float>) returns (result: array<Float>)
    requires x.Length == y.Length
    ensures result.Length == x.Length
    ensures forall i :: 0 <= i < x.Length ==>
        // Core NaN handling behavior
        (!IsNaN(x[i]) && !IsNaN(y[i]) ==> 
            result[i] == Value(Max(x[i].val, y[i].val))) &&
        (IsNaN(x[i]) && !IsNaN(y[i]) ==> 
            result[i] == y[i]) &&
        (!IsNaN(x[i]) && IsNaN(y[i]) ==> 
            result[i] == x[i]) &&
        (IsNaN(x[i]) && IsNaN(y[i]) ==> 
            IsNaN(result[i])) &&
        // Mathematical properties for non-NaN cases
        (!IsNaN(x[i]) && !IsNaN(y[i]) ==> 
            result[i].val >= x[i].val && result[i].val >= y[i].val) &&
        (!IsNaN(x[i]) && !IsNaN(y[i]) ==> 
            (result[i] == x[i] || result[i] == y[i])) &&
        // NaN preservation: result is NaN iff both inputs are NaN
        (IsNaN(result[i]) <==> (IsNaN(x[i]) && IsNaN(y[i])))
// </vc-spec>
// <vc-code>
{
  result := new Float[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant result.Length == x.Length
    invariant forall j :: 0 <= j < i ==>
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        result[j] == Value(Max(x[j].val, y[j].val))) &&
      (IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        result[j] == y[j]) &&
      (!IsNaN(x[j]) && IsNaN(y[j]) ==> 
        result[j] == x[j]) &&
      (IsNaN(x[j]) && IsNaN(y[j]) ==> 
        IsNaN(result[j])) &&
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        result[j].val >= x[j].val && result[j].val >= y[j].val) &&
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> 
        (result[j] == x[j] || result[j] == y[j])) &&
      (IsNaN(result[j]) <==> (IsNaN(x[j]) && IsNaN(y[j])))
  {
    if IsNaN(x[i]) && IsNaN(y[i]) {
      result[i] := NaN;
    } else if IsNaN(x[i]) {
      result[i] := y[i];
    } else if IsNaN(y[i]) {
      result[i] := x[i];
    } else {
      result[i] := Value(Max(x[i].val, y[i].val));
    }
    i := i + 1;
  }
}
// </vc-code>
