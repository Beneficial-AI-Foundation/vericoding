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
  assume {:axiom} false;
}
// </vc-code>
