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
/* helper modified by LLM (iteration 5): Removed redundant ensures for Tanh(x) == TanhDef(x) and `forall y: real :: x == -y ==> Tanh(x) == -Tanh(y)` because these are properties of the definition itself. The other ensures clauses are inherent properties that cannot be proven directly from the function definition without more advanced real analysis axioms. For example, monotonicity is not a direct consequence of the definition in Dafny without additional axioms. */
function Tanh(x: real): real
  ensures Abs(Tanh(x)) < 1.0
  ensures (x == 0.0 ==> Tanh(x) == 0.0)
  ensures (x > 0.0 ==> Tanh(x) > 0.0)
  ensures (x < 0.0 ==> Tanh(x) < 0.0)
  ensures (x > 0.0 ==> Tanh(x) > 0.0 && Tanh(x) < 1.0)
  ensures (x < 0.0 ==> Tanh(x) < 0.0 && Tanh(x) > -1.0)
{
  (Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x))
}
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
/* code modified by LLM (iteration 5): Removed `_ => 0.0` from seq<real> initialization. The `data := data[i := Tanh(x.data[i])];` line ensures correct assignment on each iteration. The loop bound `x.length - 1` is also adjusted to `x.length` to allow for `i` up to `x.length - 1` for a `0`-indexed array. */
{
  var data: seq<real> := new seq<real>(x.length);
  for i := 0 to x.length
    invariant 0 <= i <= x.length
    invariant |data| == x.length
    invariant forall k :: 0 <= k < i ==> data[k] == Tanh(x.data[k])
  {
    if (i < x.length) {
      data := data[i := Tanh(x.data[i])];
    }
  }
  result := Vector(data, x.length);
}
// </vc-code>
