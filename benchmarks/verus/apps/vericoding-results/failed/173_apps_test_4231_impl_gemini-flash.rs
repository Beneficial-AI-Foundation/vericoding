// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(h: int, w: int, h_selected: int, w_selected: int) -> bool {
    1 <= h <= 20 && 1 <= w <= 20 && 1 <= h_selected <= h && 1 <= w_selected <= w
}

spec fn white_cells_remaining(h: int, w: int, h_selected: int, w_selected: int) -> int
    recommends valid_input(h, w, h_selected, w_selected)
{
    (h - h_selected) * (w - w_selected)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(h: i8, w: i8, h_selected: i8, w_selected: i8) -> (result: i8)
    requires 
        valid_input(h as int, w as int, h_selected as int, w_selected as int),
    ensures 
        result as int == white_cells_remaining(h as int, w as int, h_selected as int, w_selected as int),
        result >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed syntax error in assert statement */
{
    let h_rem = (h as i32) - (h_selected as i32);
    let w_rem = (w as i32) - (w_selected as i32);

    proof {
        assert(h as int - h_selected as int >= 0);
        assert(w as int - w_selected as int >= 0);
    }

    let result_val = h_rem * w_rem;

    proof {
        assert(h as int >= 1 && h as int <= 20);
        assert(w as int >= 1 && w as int <= 20);
        assert(h_selected as int >= 1 && h_selected as int <= h as int);
        assert(w_selected as int >= 1 && w_selected as int <= w as int);

        let h_diff_spec = h as int - h_selected as int;
        let w_diff_spec = w as int - w_selected as int;

        assert(h_diff_spec >= 0);
        assert(h_diff_spec <= 19); // h_max(20) - h_selected_min(1) = 19
        assert(w_diff_spec >= 0);
        assert(w_diff_spec <= 19); // w_max(20) - w_selected_min(1) = 19

        assert(h_rem == h_diff_spec) by (nonlinear_arith);
        assert(w_rem == w_diff_spec) by (nonlinear_arith);

        assert(result_val == h_diff_spec * w_diff_spec) by (nonlinear_arith);
        assert(result_val >= 0) by (nonlinear_arith);
        assert(result_val <= 19 * 19); // 361
        assert(result_val <= 127); // i8::MAX

        assert(result_val as int == white_cells_remaining(h as int, w as int, h_selected as int, w_selected as int));
    }

    (result_val as i8)
}
// </vc-code>


}

fn main() {}