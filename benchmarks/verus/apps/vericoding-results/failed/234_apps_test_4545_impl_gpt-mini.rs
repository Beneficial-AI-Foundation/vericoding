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
/* helper modified by LLM (iteration 5): prove black_squares non-negative */
proof fn black_squares_nonneg(n: i8, a: i8)
    requires
        valid_input(n as int, a as int),
    ensures
        black_squares(n as int, a as int) >= 0,
{
    assert(black_squares(n as int, a as int) == (n as int) * (n as int) - (a as int));
    assert((a as int) <= (n as int) * (n as int));
    assert((n as int) * (n as int) - (a as int) >= 0);
}

// </vc-helpers>

// <vc-spec>
fn calculate_black_squares(n: i8, a: i8) -> (black_squares: i8)
    requires valid_input(n as int, a as int)
    ensures valid_output(n as int, a as int, black_squares as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result and handle casts with truncation */
    let res_int: int = (n as int) * (n as int) - (a as int);
    proof {
        black_squares_nonneg(n, a);
        assert(res_int == black_squares(n as int, a as int));
    }
    let tmp: i32 = #[verifier::truncate] res_int as i32;
    proof {
        assert((#[verifier::truncate] res_int as i32) == tmp);
    }
    let result: i8 = #[verifier::truncate] tmp as i8;
    proof {
        assert((#[verifier::truncate] tmp as i8) as int == res_int);
    }
    result
}

// </vc-code>


}

fn main() {}