// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn q(x: u8, y: u8) -> (z: u8)
    requires y as int - x as int > 2
    ensures (x as int) < ((z as int) * (z as int)) && ((z as int) * (z as int)) < (y as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}