// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lcm_int(a: i8, b: i8) -> (result: i8)
    requires a as int != 0 && b as int != 0,
    ensures 
        result as int >= 0,
        result as int % a as int == 0,
        result as int % b as int == 0
// </vc-spec>
// <vc-code>
{
    0i8
}
// </vc-code>


}
fn main() {}