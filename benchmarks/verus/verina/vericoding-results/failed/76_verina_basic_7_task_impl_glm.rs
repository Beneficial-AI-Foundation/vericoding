// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed divisibility proof with case analysis */
proof fn lemma_sum_of_squares_of_first_n_odd_numbers(n: u32)
    ensures
        (n as int * (2 * n as int - 1) * (2 * n as int + 1)) % 3 == 0
{
    let n_int = n as int;
    let product = n_int * (2 * n_int - 1) * (2 * n_int + 1);
    if n_int % 3 == 0 {
        assert(n_int % 3 == 0);
        assert(product % 3 == 0);
    } else if n_int % 3 == 1 {
        let a = n_int % 3;
        let b = (2 * n_int - 1) % 3;
        let c = (2 * n_int + 1) % 3;
        assert(a == 1);
        assert(b == 1);
        assert(c == 0);
        assert((a * b * c) % 3 == 0);
        assert(product % 3 == (a * b * c) % 3);
        assert(product % 3 == 0);
    } else {
        let a = n_int % 3;
        let b = (2 * n_int - 1) % 3;
        let c = (2 * n_int + 1) % 3;
        assert(a == 2);
        assert(b == 0);
        assert(c == 2);
        assert((a * b * c) % 3 == 0);
        assert(product % 3 == (a * b * c) % 3);
        assert(product % 3 == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used algebraic identity to avoid overflow */
    let n128 = n as u128;
    let num = 4 * n128 * n128 * n128 - n128;
    proof {
        lemma_sum_of_squares_of_first_n_odd_numbers(n);
        
        if n128 == 0 {
            assert(num == 0);
        } else {
            assert(n128 >= 1);
            assert(4 * n128 * n128 - 1 >= 3);
            assert(num == n128 * (4 * n128 * n128 - 1));
            assert(num >= 3);
        }
        
        let max_n = u32::MAX as u128;
        assert(n128 <= max_n);
        assert(4 * n128 * n128 * n128 <= 4 * max_n * max_n * max_n);
        assert(max_n < (1u128 << 32));
        assert(4 * max_n * max_n * max_n < (1u128 << 98));
        assert((1u128 << 98) < u128::MAX);
        assert(4 * n128 * n128 * n128 < u128::MAX);
        assert(num <= 4 * n128 * n128 * n128);
        assert(num < u128::MAX);
        assert(num <= u128::MAX);
    }
    let result = (num / 3) as u32;
    result
}
// </vc-code>

}
fn main() {}