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
/* helper modified by LLM (iteration 5): prove white_cells_remaining is non-negative */
proof fn white_nonneg(h: int, w: int, h_selected: int, w_selected: int)
    requires
        valid_input(h, w, h_selected, w_selected),
    ensures
        white_cells_remaining(h, w, h_selected, w_selected) >= 0,
{
    assert(h - h_selected >= 0);
    assert(w - w_selected >= 0);
    assert((h - h_selected) * (w - w_selected) >= 0);
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
    /* code modified by LLM (iteration 5): compute difference and prove equality to spec */
    let diff_h: i8 = h - h_selected;
    let diff_w: i8 = w - w_selected;
    let prod: i8 = diff_h * diff_w;
    let result: i8 = prod;
    proof {
        let h_i: int = h as int;
        let w_i: int = w as int;
        let hs_i: int = h_selected as int;
        let ws_i: int = w_selected as int;
        white_nonneg(h_i, w_i, hs_i, ws_i);
        assert(diff_h as int == h_i - hs_i);
        assert(diff_w as int == w_i - ws_i);
        assert(result as int == (diff_h as int) * (diff_w as int));
        assert(result as int == (h_i - hs_i) * (w_i - ws_i));
    }
    result
}

// </vc-code>


}

fn main() {}