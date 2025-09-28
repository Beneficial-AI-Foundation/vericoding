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
/* helper modified by LLM (iteration 4): Ensure validation and state initialization work with proper postconditions */
function validateSeed(seed: Option<nat>): bool {
  match seed
    case None => true
    case Some(s) => s != 0
}

lemma SeedValidationLemma(seed: Option<nat>)
  ensures validateSeed(seed) == (match seed
    case None => true
    case Some(s) => s != 0)
{
  match seed
    case None => 
    case Some(s) =>
      if s == 0 {
        // Contradiction case, but lemma ensures the equality
      }
}

function initializeState(seed: Option<nat>): (r: nat)
  requires validateSeed(seed)
  ensures seed.Some? ==> r > 0
{
  match seed
    case None => 42  // Fresh entropy placeholder
    case Some(s) => s
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
  /* code modified by LLM (iteration 4): Handle seed validation and ensure non-zero state */
  var state: nat;
  
  // Validate seed first
  if seed.Some? {
    if seed.value == 0 {
      // Invalid seed, use default
      state := 42;
    } else {
      state := seed.value;
    }
  } else {
    state := 42;
  }
  
  // Create bit generator and result
  var bitGen := BitGenerator(state, seed);
  result := Generator(bitGen, true);
  
  // We need to ensure the postcondition
  if seed.Some? {
    assert seed.value != 0 ==> result.bitGenerator.state != 0;
  }
}
// </vc-code>
