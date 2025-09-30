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
fn compute_state(seed: Option<u64>) -> (s: u64)
    ensures
        seed.is_some() ==> s != 0,
{
    let s = match seed {
        Some(x) => if x == 0u64 { 1u64 } else { x },
        None => 0u64,
    };
    s
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
    let s = compute_state(seed);
    let bg = BitGenerator { state: s, seed };
    let g = Generator { bit_generator: bg, initialized: true };
    g
}
// </vc-code>

}
fn main() {}