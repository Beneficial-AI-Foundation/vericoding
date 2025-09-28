// <vc-preamble>
// Vector datatype for fixed-length arrays
datatype Vector<T> = Vector(data: seq<T>, length: nat)
{
  predicate Valid() {
    |data| == length
  }
}

type VectorFloat = v: Vector<real> | v.Valid() witness Vector([], 0)

// Mathematical helper functions for specification
function Abs(x: real): real
  ensures Abs(x) >= 0.0
  ensures Abs(x) == x || Abs(x) == -x
  ensures x >= 0.0 ==> Abs(x) == x
  ensures x < 0.0 ==> Abs(x) == -x
{
  if x >= 0.0 then x else -x
}

// Exponential function (specification only)
function {:axiom} Exp(x: real): real
  ensures Exp(x) > 0.0

// Mathematical definition of tanh
function TanhDef(x: real): real
{
  (Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x))
}

// Main method for computing hyperbolic tangent element-wise
// </vc-preamble>

// <vc-helpers>
lemma TanhDef_Odd(x: real)
  ensures TanhDef(-x) == -TanhDef(x)
{
  calc {
    TanhDef(-x);
    (Exp(-x) - Exp(x)) / (Exp(-x) + Exp(x));
    { assert Exp(-x) - Exp(x) == -(Exp(x) - Exp(-x));
      assert Exp(-x) + Exp(x) == Exp(x) + Exp(-x); }
    -(Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x));
    -TanhDef(x);
  }
}

lemma TanhDef_Bounded(x: real)
  ensures Abs(TanhDef(x)) < 1.0
{
  calc {
    Abs(TanhDef(x));
    Abs((Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x)));
    Abs(Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x));
    < (Exp(x) + Exp(-x)) / (Exp(x) + Exp(-x));
    1.0;
  }
}

lemma TanhDef_Zero()
  ensures TanhDef(0.0) == 0.0
{
  calc {
    TanhDef(0.0);
    (Exp(0.0) - Exp(0.0)) / (Exp(0.0) + Exp(0.0));
    0.0 / (2.0 * Exp(0.0));
    0.0;
  }
}
/* helper modified by LLM (iteration 2): fixed helper functions */
// </vc-helpers>

// <vc-spec>
method ComputeTanh(x: VectorFloat) returns (result: VectorFloat)
  // No special preconditions for hyperbolic tangent
  requires true
  // Postconditions capturing the mathematical properties
  ensures result.length == x.length
  ensures forall i :: 0 <= i < x.length ==> 
    // Mathematical definition: tanh(x) = (e^x - e^(-x)) / (e^x + e^(-x))
    result.data[i] == TanhDef(x.data[i]) &&
    // Bounded property: |tanh(x)| < 1
    Abs(result.data[i]) < 1.0 &&
    // Zero property: tanh(0) = 0
    (x.data[i] == 0.0 ==> result.data[i] == 0.0) &&
    // Sign property: tanh(x) has the same sign as x (or is zero)
    (x.data[i] > 0.0 ==> result.data[i] > 0.0) &&
    (x.data[i] < 0.0 ==> result.data[i] < 0.0) &&
    // Asymptotic bounds
    (x.data[i] > 0.0 ==> result.data[i] > 0.0 && result.data[i] < 1.0) &&
    (x.data[i] < 0.0 ==> result.data[i] < 0.0 && result.data[i] > -1.0)
  // Monotonicity property: tanh is strictly increasing
  ensures forall i, j :: 0 <= i < x.length && 0 <= j < x.length && x.data[i] < x.data[j] ==> 
    result.data[i] < result.data[j]
  // Odd function property: tanh(-x) = -tanh(x)
  ensures forall i, j :: 0 <= i < x.length && 0 <= j < x.length && x.data[i] == -x.data[j] ==> 
    result.data[i] == -result.data[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed loop invariant syntax */
  var newData := new real[x.length];
  for i := 0 to x.length
    invariant 0 <= i <= x.length
    invariant forall j | 0 <= j < i :: newData[j] == TanhDef(x.data[j])
  {
    newData[i] := TanhDef(x.data[i]);
  }
  result := Vector(newData[..x.length], x.length);
}
// </vc-code>
