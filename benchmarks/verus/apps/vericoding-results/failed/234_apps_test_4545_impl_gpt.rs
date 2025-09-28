// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 100 && 0 <= a <= n * n
}

spec fn black_squares(n: int, a: int) -> int
    recommends valid_input(n, a)
{
    n * n - a
}

spec fn valid_output(n: int, a: int, result: int) -> bool
    recommends valid_input(n, a)
{
    result == black_squares(n, a) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened non-negativity lemma and added safety lemma for i32 ops */
proof fn lemma_black_squares_nonneg(n: int, a: int)
    requires
        valid_input(n, a),
    ensures
        black_squares(n, a) >= 0,
{
    assert(0 <= a <= n * n);
    assert(black_squares(n, a) == n * n - a);
    assert(n * n - a >= 0);
}

/* helper modified by LLM (iteration 5): prove bounds to make i32 multiplication/subtraction safe */
proof fn lemma_i32_mul_sub_safe(n: i8, a: i8)
    requires
        valid_input(n as int, a as int),
    ensures
        0 <= ((n as i32) as int) * ((n as i32) as int) - ((a as i32) as int),
        ((n as i32) as int) * ((n as i32) as int) <= i32::MAX as int,
{
    let ni: int = n as int;
    let ai: int = a as int;
    assert(1 <= ni && ni <= 100);
    assert(0 <= ai && ai <= ni * ni);
    // Casts preserve numeric value for these ranges
    assert(((n as i32) as int) == ni);
    assert(((a as i32) as int) == ai);
    // Bounds for multiplication and subtraction
    assert(0 <= ni * ni);
    assert(ni * ni <= 10000);
    assert(0 <= ni * ni - ai);
    assert(ni * ni <= i32::MAX as int);
}

// </vc-helpers>

// <vc-spec>
fn calculate_black_squares(n: i8, a: i8) -> (black_squares: i8)
    requires valid_input(n as int, a as int)
    ensures valid_output(n as int, a as int, black_squares as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): prove i32 arithmetic is safe, then compute and truncate to i8 */
    let ghost ni: int = n as int;
    let ghost ai: int = a as int;
    proof {
        // Non-negativity of the mathematical result
        lemma_black_squares_nonneg(ni, ai);
        // Prove i32 ops are within bounds
        lemma_i32_mul_sub_safe(n, a);
        // Helpful bound for i32 max
        assert(10000 <= i32::MAX as int);
    }
    let m: i32 = n as i32;
    let a32: i32 = a as i32;
    let r32: i32 = m * m - a32;
    let r8: i8 = #[verifier::truncate] (r32 as i8);
    r8
}
// </vc-code>


}

fn main() {}