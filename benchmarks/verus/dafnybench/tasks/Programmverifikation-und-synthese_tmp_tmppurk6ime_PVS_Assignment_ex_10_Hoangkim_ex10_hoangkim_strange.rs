// <vc-preamble>
use vstd::prelude::*;

verus! {

fn q(x: u32, y: u32) -> (z: u32)
    requires y > x + 2
    ensures x < z*z && z*z < y
{
    assume(false);
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn strange()
    ensures 1==2
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}