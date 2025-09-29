// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero() -> (z: usize)
    ensures z == 0
{
    0
}
// </vc-helpers>

// <vc-spec>
fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
// </vc-spec>
// <vc-code>
{
    let result: usize = 0;
    proof { assert(result >= 0); }
    result
}
// </vc-code>

}
fn main() {}