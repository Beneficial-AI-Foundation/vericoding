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
// Helper function to create an initialized BitGenerator
function createBitGenerator(seed: Option<nat>): BitGenerator
{
  BitGenerator(
    (if seed.Some? then seed.value + 1 else 1),
    seed
  )
}

// Helper predicate to verify BitGenerator is properly initialized
predicate isValidBitGenerator(bg: BitGenerator, seed: Option<nat>)
{
  bg.seed == seed &&
  (seed.Some? ==> bg.state != 0)
}
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
  /* code modified by LLM (iteration 2): fixed BitGenerator constructor syntax */
  var bitGen := createBitGenerator(seed);
  result := Generator(
    bitGen,
    true
  );
}
// </vc-code>
