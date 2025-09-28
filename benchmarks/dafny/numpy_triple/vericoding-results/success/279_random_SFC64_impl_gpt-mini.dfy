// <vc-preamble>
// SFC64 state containing 256 bits split into four 64-bit words
datatype SFC64State = SFC64State(a: bv64, b: bv64, c: bv64, counter: bv64)

// Option type for optional seed parameter
datatype Option<T> = None | Some(value: T)

// SFC64 initialization method that creates a 256-bit state from an optional seed
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): create state from seed */
function MakeStateFromSeed(v: bv64): SFC64State
{
  SFC64State(v, v + 1, v + 2, v + 3)
}

/* helper modified by LLM (iteration 2): prove at least one component non-zero */
lemma MakeStateFromSeed_nonzero(v: bv64)
  ensures MakeStateFromSeed(v).a != 0 || MakeStateFromSeed(v).b != 0 || MakeStateFromSeed(v).c != 0 || MakeStateFromSeed(v).counter != 0
{
  if v != 0 {
    assert MakeStateFromSeed(v).a == v;
    assert v != 0;
  } else {
    // when v == 0, b == 1 (nonzero)
    assert MakeStateFromSeed(v).b == v + 1;
    assert MakeStateFromSeed(v).b != 0;
  }
}
// </vc-helpers>

// <vc-spec>
method SFC64(seed: Option<bv64>) returns (state: SFC64State)
  // If no seed provided, initialize state to all zeros
  ensures seed.None? ==> state.a == 0 && state.b == 0 && state.c == 0 && state.counter == 0
  // If seed provided, at least one component should be non-zero (proper initialization)
  ensures seed.Some? ==> (state.a != 0 || state.b != 0 || state.c != 0 || state.counter != 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize state based on optional seed and call helper */
{
  if seed.None? {
    state := SFC64State(0, 0, 0, 0);
  } else {
    match seed {
      case Some(v) =>
        state := MakeStateFromSeed(v);
        MakeStateFromSeed_nonzero(v);
    }
  }
}
// </vc-code>
