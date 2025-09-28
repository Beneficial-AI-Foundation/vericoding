// <vc-preamble>
use vstd::prelude::*;

verus! {

struct BitGenerator {

    state: u64,

    seed: Option<u64>,
}

struct Generator {

    bit_generator: BitGenerator,

    initialized: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): compute nonzero state from optional seed */
fn compute_state(seed: Option<u64>) -> (result: u64)
    ensures
        seed.is_some() ==> result != 0u64,
{
    let result = match seed {
        Some(s) => if s == 0u64 { 1u64 } else { s },
        None => 0u64,
    };
    result
}
// </vc-helpers>

// <vc-spec>
fn default_rng(seed: Option<u64>) -> (result: Generator)
    ensures
        result.initialized == true,
        result.bit_generator.seed == seed,
        seed.is_some() ==> result.bit_generator.state != 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): initialize generator using compute_state */
    let bg = BitGenerator { state: compute_state(seed), seed: seed };
    let result = Generator { bit_generator: bg, initialized: true };
    result
}
// </vc-code>

}
fn main() {}