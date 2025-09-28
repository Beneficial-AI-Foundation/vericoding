// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): return named constant 636619772 */
fn const_636619772() -> (result: i32)
    ensures
        result == 636619772,
{
    let result: i32 = 636619772;
    result
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
    /* code modified by LLM (iteration 4): call helper to produce npy_2_pi */
    let v: i32 = const_636619772();
    v
}
// </vc-code>


}
fn main() {}