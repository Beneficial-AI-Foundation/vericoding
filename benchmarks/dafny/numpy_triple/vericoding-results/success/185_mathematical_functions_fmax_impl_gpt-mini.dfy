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
lemma Max_ge(x: real, y: real) ensures Max(x,y) >= x && Max(x,y) >= y {
  if x >= y {
    assert Max(x,y) == x;
    assert Max(x,y) >= x;
    assert x >= y ==> Max(x,y) >= y;
    // from Max(x,y) == x and x >= y we get Max(x,y) >= y
  } else {
    assert Max(x,y) == y;
    assert Max(x,y) >= y;
    assert y > x ==> Max(x,y) >= x;
    // from Max(x,y) == y and y > x we get Max(x,y) >= x
  }
}

lemma Max_is_one_of(x: real, y: real) ensures Max(x,y) == x || Max(x,y) == y {
  if x >= y {
    assert Max(x,y) == x;
  } else {
    assert Max(x,y) == y;
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
    invariant forall k :: 0 <= k < i ==>
        (!IsNaN(x[k]) && !IsNaN(y[k]) ==> 
            result[k] == Value(Max(x[k].val, y[k].val))) &&
        (IsNaN(x[k]) && !IsNaN(y[k]) ==> 
            result[k] == y[k]) &&
        (!IsNaN(x[k]) && IsNaN(y[k]) ==> 
            result[k] == x[k]) &&
        (IsNaN(x[k]) && IsNaN(y[k]) ==> 
            IsNaN(result[k])) &&
        (!IsNaN(x[k]) && !IsNaN(y[k]) ==> 
            result[k].val >= x[k].val && result[k].val >= y[k].val) &&
        (!IsNaN(x[k]) && !IsNaN(y[k]) ==> 
            (result[k] == x[k] || result[k] == y[k])) &&
        (IsNaN(result[k]) <==> (IsNaN(x[k]) && IsNaN(y[k])))
  {
    if !IsNaN(x[i]) && !IsNaN(y[i]) {
      if x[i].val >= y[i].val {
        result[i] := x[i];
      } else {
        result[i] := y[i];
      }
    } else if IsNaN(x[i]) && !IsNaN(y[i]) {
      result[i] := y[i];
    } else if !IsNaN(x[i]) && IsNaN(y[i]) {
      result[i] := x[i];
    } else {
      result[i] := NaN;
    }
    i := i + 1;
  }
}

// </vc-code>
