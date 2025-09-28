// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed-point constant for pi/2 */
fn fixed_pi_2_1000() -> (result: i32)
    ensures
        result == 1571,
{
    1571
}

/* helper modified by LLM (iteration 5): proof that doubling of literal is 3142 (avoids calling exec fn in spec) */
fn fixed_pi_2_double_exact()
    ensures
        2 * (1571 as int) == 3142,
{
    proof {
        assert(2 * (1571 as int) == 3142);
    }
}

// </vc-helpers>

// <vc-spec>
fn npy_pi_2() -> (result: i32)
    ensures
        /* π/2 is approximately 1.5708... represented as fixed point */
        1570 < result < 1571,
        /* Basic sanity check: π/2 is between 1 and 2 */
        1000 < result < 2000,
        /* 2*(π/2) should be approximately π (3.14159...) */
        3141 < 2 * (result as int) < 3142,
        /* (π/2)/2 = π/4 is approximately 0.7854... */
        785 < (result as int) / 2 < 786,
        /* 3*(π/2) = 3π/2 is approximately 4.7124... (270 degrees) */
        4712 < 3 * (result as int) < 4713,
        /* 4*(π/2) = 2π is approximately 6.2832... (full circle) */
        6283 < 4 * (result as int) < 6284,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return fixed-point approximation using helper */
    let result: i32 = fixed_pi_2_1000();
    result
}
// </vc-code>


}
fn main() {}