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
function FMaxFloat(a: Float, b: Float): Float {
  if IsNaN(a) then
    if IsNaN(b) then NaN else b
  else
    if IsNaN(b) then a else Value(Max(a.val, b.val))
}
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
  var n := x.Length;
  result := new Float[n] (i => NaN);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
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
    decreases n - i
  {
    var xi := x[i];
    var yi := y[i];
    if IsNaN(xi) {
      if IsNaN(yi) {
        result[i] := NaN;
      } else {
        result[i] := yi;
      }
    } else {
      if IsNaN(yi) {
        result[i] := xi;
      } else {
        var xv := xi.val;
        var yv := yi.val;
        if xv >= yv {
          result[i] := xi;
        } else {
          result[i] := yi;
        }
      }
    }
    i := i + 1;
  }
}
// </vc-code>
