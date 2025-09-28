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
  /* code modified by LLM (iteration 3): Add loop with invariants to prove postconditions */
  var res := new Float[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==>
      // Core NaN handling
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> res[j] == Value(Max(x[j].val, y[j].val))) &&
      (IsNaN(x[j]) && !IsNaN(y[j]) ==> res[j] == y[j]) &&
      (!IsNaN(x[j]) && IsNaN(y[j]) ==> res[j] == x[j]) &&
      (IsNaN(x[j]) && IsNaN(y[j]) ==> IsNaN(res[j])) &&
      // Mathematical properties
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> res[j].val >= x[j].val && res[j].val >= y[j].val) &&
      (!IsNaN(x[j]) && !IsNaN(y[j]) ==> (res[j] == x[j] || res[j] == y[j])) &&
      // NaN preservation
      (IsNaN(res[j]) <==> (IsNaN(x[j]) && IsNaN(y[j])))
  {
    if !IsNaN(x[i]) && !IsNaN(y[i]) {
      res[i] := Value(Max(x[i].val, y[i].val));
    } else if IsNaN(x[i]) && !IsNaN(y[i]) {
      res[i] := y[i];
    } else if !IsNaN(x[i]) && IsNaN(y[i]) {
      res[i] := x[i];
    } else {
      res[i] := NaN;
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
