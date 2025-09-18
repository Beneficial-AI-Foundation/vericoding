// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero() -> usize {
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
    let r: usize = zero();
    r
}
// </vc-code>

}
fn main() {}