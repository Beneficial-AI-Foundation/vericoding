// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, r: int) -> bool {
    n >= 1 && r >= 1
}

spec fn expected_result(n: int, r: int) -> int {
    if valid_input(n, r) {
        let k = if r < n - 1 { r } else { n - 1 };
        k * (k + 1) / 2 + if r >= n { 1int } else { 0int }
    } else {
        0int
    }
}

fn solve_shapes(n: i8, r: i8) -> (result: i8)
    requires valid_input(n as int, r as int)
    ensures result as int == expected_result(n as int, r as int)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by adding an empty body to the proof function */
proof fn lemma_min_equiv(r: i8, n: i8)
    requires
        r >= 1,
        n >= 1,
    ensures
        (if r < n - 1 { r } else { n - 1 }) as int ==
        if r as int < (n as int) - 1 { r as int } else { (n as int) - 1 }
{
}

// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): resubmitting previous logic after fixing helper compilation error. */
    let k = if r < n - 1 {
        r
    } else {
        n - 1
    };

    let k_wide = k as i64;
    let sum_wide = k_wide * (k_wide + 1) / 2;

    let mut result_wide = sum_wide;
    if r >= n {
        result_wide = result_wide + 1;
    }

    proof {
        let n_int = n as int;
        let r_int = r as int;

        lemma_min_equiv(r, n);

        let k_spec = if r_int < n_int - 1 { r_int } else { n_int - 1 };
        assert(k as int == k_spec);

        let sum_spec = k_spec * (k_spec + 1) / 2;
        assert(sum_wide as int == sum_spec);

        let expected = expected_result(n_int, r_int);

        if r >= n {
            assert(result_wide as int == sum_spec + 1);
        } else {
            assert(result_wide as int == sum_spec);
        }
        assert(result_wide as int == expected);
    }

    result_wide as i8
}
// </vc-code>


}

fn main() {}