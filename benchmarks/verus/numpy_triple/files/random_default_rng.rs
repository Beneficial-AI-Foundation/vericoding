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

fn default_rng(seed: Option<u64>) -> (result: Generator)
    ensures
        result.initialized == true,
        result.bit_generator.seed == seed,
        seed.is_some() ==> result.bit_generator.state != 0,
{
    assume(false);
    unreached()
}

}
fn main() {}