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
/* helper modified by LLM (iteration 5): spec initial_state and lemma proving nonzero when seed is Some */
spec fn initial_state(seed: Option<u64>) -> u64 {
    match seed {
        Some(s) => if s == u64::MAX { s } else { s.wrapping_add(1) },
        None => 0u64,
    }
}

proof fn initial_state_nonzero(seed: Option<u64>) ensures seed.is_some() ==> initial_state(seed) != 0 {
    match seed {
        Some(s) => {
            if s == u64::MAX {
                assert(initial_state(seed) == s);
                assert(s != 0u64);
            } else {
                assert(initial_state(seed) == s.wrapping_add(1));
                assert(initial_state(seed) != 0u64);
            }
        },
        None => {}
    }
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
    /* code modified by LLM (iteration 5): initialize Generator deterministically from seed */
    let state: u64 = match seed {
        Some(s) => if s == u64::MAX { s } else { s.wrapping_add(1) },
        None => 0u64,
    };
    let bg = BitGenerator { state: state, seed: seed };
    let result = Generator { bit_generator: bg, initialized: true };
    result
}
// </vc-code>

}
fn main() {}