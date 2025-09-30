// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_npy_2_pi_bounds()
    ensures
        636619772i32 > 636000000i32,
        636619772i32 < 637000000i32,
{
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
    proof { lemma_npy_2_pi_bounds(); }
    636619772i32
}
// </vc-code>


}
fn main() {}