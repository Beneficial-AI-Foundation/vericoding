// <vc-preamble>
// SFC64 state containing 256 bits split into four 64-bit words
datatype SFC64State = SFC64State(a: bv64, b: bv64, c: bv64, counter: bv64)

// Option type for optional seed parameter
datatype Option<T> = None | Some(value: T)

// SFC64 initialization method that creates a 256-bit state from an optional seed
// </vc-preamble>

// <vc-helpers>
function RotL64(x: bv64, k: nat): bv64
  requires k < 64
{
  (x << k) | (x >> (64 - k))
}

function SFC64Step(state: SFC64State): SFC64State
{
    var tmp := state.a + state.b + state.counter;
    var new_a := state.b ^ (state.b >> 11);
    var new_b := state.c + (state.c << 3);
    var new_c := RotL64(state.c, 24) + tmp;
    SFC64State(new_a, new_b, new_c, state.counter + 1)
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
{
  /* code modified by LLM (iteration 2): Fixed bitvector literal syntax. */
  if seed.None? {
    state := SFC64State(0 as bv64, 0 as bv64, 0 as bv64, 0 as bv64);
  } else {
    // Initialize with seed and constants derived from golden ratio, then warm up.
    var current_state := SFC64State(seed.value, 0x9e3779b97f4a7c15 as bv64, 0x9e3779b97f4a7c15 as bv64, 1 as bv64);
    var i := 0;
    while i < 12
      invariant i <= 12
      invariant current_state.counter == (1 as bv64) + (i as bv64)
    {
      current_state := SFC64Step(current_state);
      i := i + 1;
    }
    state := current_state;
  }
}
// </vc-code>
