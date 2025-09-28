// <vc-preamble>
// Floating-point number type to model Float from Lean
type Float = real

// Container for random state with seed-based initialization
datatype RandomState = RandomState(seed: nat)

// Pure function that deterministically maps state to result
// This ensures the same seed always produces the same result
ghost function RandomValue(state: RandomState): Float

// Generates a random float in the range [0, 1) using the RandomState
// This models the RandomState.random() method which is the most fundamental
// operation for generating uniformly distributed random numbers.
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed while loop condition syntax using proper comparison operators */
function floor(x: real): int
{
  if x >= 0.0 then
    var i : int := 0;
    while i as real <= x
      invariant i as real <= x + 1.0
    {
      i := i + 1;
    }
    i - 1
  else
    var i : int := 0;
    while i as real > x
      invariant i as real >= x - 1.0
    {
      i := i - 1;
    }
    i
}

ghost function RandomValue(state: RandomState): Float
  ensures 0.0 <= RandomValue(state) < 1.0
{
  // Deterministic mapping from seed to [0,1) using fractional part
  var fractional := (state.seed as real) * 0.6180339887498948482;  // Golden ratio conjugate
  fractional - (floor(fractional) as real)
}
// </vc-helpers>

// <vc-spec>
method random(state: RandomState) returns (result: Float)
  ensures 0.0 <= result < 1.0  // Result is always in the range [0, 1)
  ensures result == RandomValue(state)  // Deterministic: same seed produces same result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Direct implementation using helper function */
{
  result := RandomValue(state);
}
// </vc-code>
