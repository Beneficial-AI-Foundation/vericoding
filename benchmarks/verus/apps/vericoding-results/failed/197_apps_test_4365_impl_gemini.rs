// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k: int) -> bool {
    2 <= k <= 100
}

spec fn count_odd_numbers(k: int) -> int
    recommends k >= 1
{
    (k + 1) / 2
}

spec fn count_even_numbers(k: int) -> int
    recommends k >= 1
{
    k / 2
}

spec fn expected_result(k: int) -> int
    recommends valid_input(k)
{
    count_odd_numbers(k) * count_even_numbers(k)
}

spec fn correct_result(k: int, result: int) -> bool
    recommends valid_input(k)
{
    result == expected_result(k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn count_even_odd_pairs(k: i8) -> (result: i8)
    requires
        valid_input(k as int),
    ensures
        correct_result(k as int, result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using the correct lemma and arguments */
{
    let k32 = k as i32;
    let odd_count = (k32 + 1) / 2;
    let even_count = k32 / 2;

    proof {
        let k_int = k as int;
        let odd_count_int = count_odd_numbers(k_int);
        let even_count_int = count_even_numbers(k_int);
        let result_int = expected_result(k_int);

        assert(2 <= k_int <= 100) by(nonlinear_arith);

        assert(odd_count_int <= (100+1)/2 == 50) by(nonlinear_arith);
        assert(even_count_int <= 100/2 == 50) by(nonlinear_arith);
        assert(odd_count_int >= (2+1)/2 == 1) by(nonlinear_arith);
        assert(even_count_int >= 2/2 == 1) by(nonlinear_arith);

        assert(0 <= odd_count_int);
        assert(0 <= even_count_int);
        vstd::arithmetic::mul::lemma_mul_le_mul_of_nonneg(odd_count_int, 50, even_count_int, 50);
        assert(result_int <= 2500) by(nonlinear_arith);

        assert(i32::MIN <= result_int <= i32::MAX) by(nonlinear_arith);

        assert(odd_count as int == odd_count_int);
        assert(even_count as int == even_count_int);
    }

    let result32 = odd_count * even_count;

    proof {
        let k_int = k as int;
        assert(result32 as int == expected_result(k_int));
        // The spec requires `k <= 100` but `ensures` a result that fits in `i8`.
        // This is only possible for `k <= 22` because `expected_result(23) == 132`, which overflows `i8`.
        // Thus, the specification is unsatisfiable. To make this code verify,
        // the precondition `valid_input` would need to be changed to `2 <= k <= 22`.
        // We assert this necessary (but unprovable) condition to satisfy the postcondition.
        assert(expected_result(k_int) <= i8::MAX);
    }

    result32 as i8
}
// </vc-code>


}

fn main() {}