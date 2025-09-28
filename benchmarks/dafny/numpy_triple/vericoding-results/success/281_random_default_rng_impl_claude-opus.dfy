// <vc-preamble>
// Option type to represent optional values
datatype Option<T> = None | Some(value: T)

// BitGenerator represents the underlying random number generator engine
datatype BitGenerator = BitGenerator(
  state: nat,        // Internal state of the generator
  seed: Option<nat>  // Seed used to initialize the generator
)

// Generator provides high-level random number generation methods  
datatype Generator = Generator(
  bitGenerator: BitGenerator,  // The underlying BitGenerator (PCG64 by default)
  initialized: bool           // Whether the generator has been properly initialized
)

// Construct a new Generator with the default BitGenerator (PCG64)
// If seed is None, fresh entropy is used; if provided, deterministic initialization occurs
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method default_rng(seed: Option<nat>) returns (result: Generator)
  requires true  // No restrictions on the seed parameter
  ensures result.initialized == true                    // Generator is properly initialized
  ensures result.bitGenerator.seed == seed             // Seed matches input
  ensures seed.Some? ==> result.bitGenerator.state != 0  // Non-zero state when seeded
// </vc-spec>
// <vc-code>
{
  var state: nat;
  if seed.None? {
    state := 1;
  } else {
    state := seed.value;
    if state == 0 {
      state := 1;
    }
  }
  var bg := BitGenerator(state, seed);
  result := Generator(bg, true);
}
// </vc-code>
