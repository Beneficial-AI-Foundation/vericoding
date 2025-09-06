/* SFC64 pseudo-random number generator with 256-bit state

Specification: SFC64 initializes a 256-bit state from seed

BitGenerator for the SFC64 pseudo-random number generator

SFC64 is a chaotic RNG that uses a 256-bit state. It is very fast and appears to be very robust to statistical tests.

Parameters:
- seed : None, int, array_like[ints], SeedSequence, BitGenerator, Generator
    A seed to initialize the BitGenerator */

use vstd::prelude::*;

verus! {

/* SFC64 state containing 256 bits split into four 64-bit words */
struct SFC64State {
    a: u64,
    b: u64,
    c: u64,
    counter: u64,
}
fn sfc64(seed: Option<u64>) -> (result: SFC64State)
    ensures
        seed.is_none() ==> (result.a == 0 && result.b == 0 && result.c == 0 && result.counter == 0),
        seed.is_some() ==> (result.a != 0 || result.b != 0 || result.c != 0 || result.counter != 0),
{
    // impl-start
    assume(false);
    SFC64State { a: 0, b: 0, c: 0, counter: 0 }
    // impl-end
}
}
fn main() {}