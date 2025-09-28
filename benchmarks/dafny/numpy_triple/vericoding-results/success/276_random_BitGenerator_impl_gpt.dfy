// <vc-preamble>
// UInt64 type to match the Lean source specification
newtype UInt64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

// Optional type for representing seed values
datatype Option<T> = None | Some(value: T)

// BitGenerator state representing the internal state of a pseudo-random number generator
datatype BitGeneratorState = BitGeneratorState(
  // The seed value used to initialize the generator, or None if no seed was provided
  seed: Option<UInt64>,
  // The internal state of the generator used for random number generation
  internal_state: UInt64
)

// Helper predicate to check if an Option contains a value
predicate IsSome<T>(opt: Option<T>)
{
  opt.Some?
}

// Helper predicate to check if an Option is None
predicate IsNone<T>(opt: Option<T>)
{
  opt.None?
}

/**
 * BitGenerator initialization method that creates a properly initialized BitGenerator state.
 * This corresponds to numpy.random.BitGenerator constructor.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced invalid newtype construction with explicit cast for UInt64 and encoded initialization rule */
function ChooseInitialState(seed: Option<UInt64>): UInt64
  ensures seed.Some? ==> ChooseInitialState(seed) != 0
  ensures seed.None? ==> ChooseInitialState(seed) == 0
{
  if seed.Some? then 1 as UInt64 else 0 as UInt64
}
// </vc-helpers>

// <vc-spec>
method NumpyRandomBitGenerator(seed: Option<UInt64>) returns (result: BitGeneratorState)
  requires true  // Any seed value is valid, including None
  ensures result.seed == seed
  ensures seed.Some? ==> result.internal_state != 0
  ensures seed.None? ==> result.internal_state == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use helper to derive internal_state and build result */
  var init := ChooseInitialState(seed);
  result := BitGeneratorState(seed, init);
}
// </vc-code>
