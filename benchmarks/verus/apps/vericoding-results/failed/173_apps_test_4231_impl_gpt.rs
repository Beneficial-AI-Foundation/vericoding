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
/* helper modified by LLM (iteration 4): prove non-negativity of differences and restate definition */
proof fn lemma_diff_nonneg(h: int, w: int, h_selected: int, w_selected: int)
    requires
        valid_input(h, w, h_selected, w_selected),
    ensures
        0 <= h - h_selected,
        0 <= w - w_selected,
{
    assert(h_selected <= h);
    assert(w_selected <= w);
    assert(0 <= h - h_selected);
    assert(0 <= w - w_selected);
}

/* helper modified by LLM (iteration 4): restate white_cells_remaining definition (direct from spec) */
proof fn lemma_white_cells_def(h: int, w: int, h_selected: int, w_selected: int)
    requires
        valid_input(h, w, h_selected, w_selected),
    ensures
        white_cells_remaining(h, w, h_selected, w_selected) == (h - h_selected) * (w - w_selected),
{
    assert(white_cells_remaining(h, w, h_selected, w_selected) == (h - h_selected) * (w - w_selected));
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
    /* code modified by LLM (iteration 4): compute using wider machine integers in exec and keep mathematical reasoning in proof */
    proof {
        let ghost hi: int = h as int;
        let ghost wi: int = w as int;
        let ghost hsi: int = h_selected as int;
        let ghost wsi: int = w_selected as int;
        lemma_diff_nonneg(hi, wi, hsi, wsi);
        lemma_white_cells_def(hi, wi, hsi, wsi);
    }

    let dh: i32 = (h as i32) - (h_selected as i32);
    let dw: i32 = (w as i32) - (w_selected as i32);
    let prod: i32 = dh * dw;

    let result: i8 = prod as i8;

    result
}
// </vc-code>


}

fn main() {}