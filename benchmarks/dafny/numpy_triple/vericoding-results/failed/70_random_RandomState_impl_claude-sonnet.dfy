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
/* helper modified by LLM (iteration 5): remove axiom and provide concrete implementation */
function RandomValueImpl(state: RandomState): Float
{
  var normalized := (state.seed as real) / 4294967296.0;
  if normalized >= 1.0 then normalized - 1.0 else normalized
}

lemma RandomValueBounds(state: RandomState)
  ensures 0.0 <= RandomValueImpl(state) < 1.0
{
  var normalized := (state.seed as real) / 4294967296.0;
  assert state.seed >= 0;
  assert normalized >= 0.0;
  if normalized >= 1.0 {
    assert RandomValueImpl(state) == normalized - 1.0;
    assert RandomValueImpl(state) >= 0.0;
    assert RandomValueImpl(state) < 1.0;
  } else {
    assert RandomValueImpl(state) == normalized;
    assert RandomValueImpl(state) >= 0.0;
    assert RandomValueImpl(state) < 1.0;
  }
}
// </vc-helpers>

// <vc-spec>
method random(state: RandomState) returns (result: Float)
  ensures 0.0 <= result < 1.0  // Result is always in the range [0, 1)
  ensures result == RandomValue(state)  // Deterministic: same seed produces same result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use non-ghost function implementation */
  RandomValueBounds(state);
  result := RandomValueImpl(state);
  assert result == RandomValueImpl(state);
  assert 0.0 <= result < 1.0;
}
// </vc-code>
