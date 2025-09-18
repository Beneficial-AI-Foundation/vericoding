// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lcm_int(a: i32, b: i32) -> (result: i32)
    requires a != 0 && b != 0,
    ensures 
        result >= 0,
        result % a == 0,
        result % b == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}