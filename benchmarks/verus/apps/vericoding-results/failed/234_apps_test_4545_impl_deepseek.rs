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
proof fn lemma_mul_in_range(n: int, a: int)
    requires
        valid_input(n, a),
    ensures
        n * n - a >= 0,
        n * n - a <= 10000
{
    assert(n >= 1 && n <= 100);
    assert(a >= 0 && a <= n * n);
    proof {
        let max_sq = 100 * 100;
        assert(n * n <= max_sq);
        assert(n * n - a >= 0 && n * n - a <= max_sq);
    }
}
// </vc-helpers>

// <vc-spec>
fn calculate_black_squares(n: i8, a: i8) -> (black_squares: i8)
    requires valid_input(n as int, a as int)
    ensures valid_output(n as int, a as int, black_squares as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow handling and verification */
    proof {
        lemma_mul_in_range(n as int, a as int);
    }
    let n_i32: i32 = i32::from(n);
    let a_i32: i32 = i32::from(a);
    let n_sq: i32 = n_i32.checked_mul(n_i32).unwrap();
    let result_i32: i32 = n_sq.checked_sub(a_i32).unwrap();
    let black_squares: i8 = result_i32.try_into().unwrap();
    black_squares
}
// </vc-code>


}

fn main() {}