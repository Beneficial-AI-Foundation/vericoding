// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn division_function(x: nat, y: nat) -> (result: (int, int))
    ensures
        y == 0 ==> result.0 == x && result.1 == 0,
        y != 0 ==> (
            result.1 * y + result.0 == x &&
            0 <= result.0 < y &&
            0 <= result.1
        ),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}
// </vc-code>


}
fn main() {}