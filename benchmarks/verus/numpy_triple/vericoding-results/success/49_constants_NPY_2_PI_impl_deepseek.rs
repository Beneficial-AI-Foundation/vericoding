// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn npy_2_pi_helper() -> (result: i32)
    ensures
        result == 636619772,
        result > 636000000,
        result < 637000000,
{
    636619772
}
// </vc-helpers>

// <vc-spec>
fn npy_2_pi() -> (result: i32)
    ensures
        result == 636619772,
        result > 636000000,
        result < 637000000,
// </vc-spec>
// <vc-code>
{
    let result = npy_2_pi_helper();
    result
}
// </vc-code>


}
fn main() {}