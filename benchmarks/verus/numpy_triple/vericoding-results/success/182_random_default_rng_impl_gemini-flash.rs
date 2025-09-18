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
proof fn lemma_u64_nonzero_implies_not_zero(x: u64) ensures x != 0 ==> x != 0 {}
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
    let initial_state = if seed.is_some() { seed.unwrap() } else { 0xDEADC0DEu64 };
    let final_state = if initial_state == 0 { 0xDEADC0DEu64 } else { initial_state };

    if initial_state == 0 && seed.is_some() && seed.unwrap() == 0 {
        proof {
            assert(seed.is_some());
            assert(seed.unwrap() == 0);
        }
    }

    Generator {
        bit_generator: BitGenerator {
            state: final_state,
            seed: seed,
        },
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}