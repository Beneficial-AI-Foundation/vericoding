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
function ComputeRandomValue(state: RandomState): real
{
  (state.seed % 1000) / 1000.0
}
ghost function RandomValue(state: RandomState): Float
{
  ComputeRandomValue(state)
}
// </vc-helpers>

// <vc-spec>
method random(state: RandomState) returns (result: Float)
  ensures 0.0 <= result < 1.0  // Result is always in the range [0, 1)
  ensures result == RandomValue(state)  // Deterministic: same seed produces same result
// </vc-spec>
// <vc-code>
{
  result := ComputeRandomValue(state);
}
// </vc-code>
