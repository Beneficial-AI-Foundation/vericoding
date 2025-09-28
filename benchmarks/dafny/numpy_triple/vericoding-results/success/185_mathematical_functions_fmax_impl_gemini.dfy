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
function Fmax_element(fx: Float, fy: Float): (fz: Float)
    ensures (!IsNaN(fx) && !IsNaN(fy) ==> fz == Value(Max(fx.val, fy.val))) &&
            (IsNaN(fx) && !IsNaN(fy) ==> fz == fy) &&
            (!IsNaN(fx) && IsNaN(fy) ==> fz == fx) &&
            (IsNaN(fx) && IsNaN(fy) ==> IsNaN(fz)) &&
            (!IsNaN(fx) && !IsNaN(fy) ==> fz.val >= fx.val && fz.val >= fy.val) &&
            (!IsNaN(fx) && !IsNaN(fy) ==> (fz == fx || fz == fy)) &&
            (IsNaN(fz) <==> (IsNaN(fx) && IsNaN(fy)))
{
    match fx {
        case NaN => 
            match fy {
                case NaN => NaN
                case Value(_) => fy
            }
        case Value(vx) => 
            match fy {
                case NaN => fx
                case Value(vy) => Value(Max(vx, vy))
            }
    }
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
  result := new Float[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant result.Length == x.Length
    invariant forall j :: 0 <= j < i ==> result[j] == Fmax_element(x[j], y[j])
  {
    result[i] := Fmax_element(x[i], y[i]);
    i := i + 1;
  }
}
// </vc-code>
