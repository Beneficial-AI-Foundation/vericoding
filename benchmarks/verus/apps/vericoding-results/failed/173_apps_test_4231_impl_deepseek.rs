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
/* helper modified by LLM (iteration 5): Removed int arithmetic from exec code, using i8 operations with proof of correctness */
fn calculate_remaining(h: i8, w: i8, h_sel: i8, w_sel: i8) -> (result: i8)
    requires
        1 <= h <= 20,
        1 <= w <= 20,
        1 <= h_sel <= h,
        1 <= w_sel <= w,
    ensures
        result as int == (h as int - h_sel as int) * (w as int - w_sel as int),
        result >= 0,
{
    let diff_h = h - h_sel;
    let diff_w = w - w_sel;
    proof {
        assert(0 <= diff_h as int <= 19);
        assert(0 <= diff_w as int <= 19);
        assert(0 <= (diff_h as int) * (diff_w as int) <= 361);
    }
    diff_h * diff_w
}
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
{
    /* code modified by LLM (iteration 5): Fixed by calling verified helper function */
    let result = calculate_remaining(h, w, h_selected, w_selected);
    result
}
// </vc-code>


}

fn main() {}