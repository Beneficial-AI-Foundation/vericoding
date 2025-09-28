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
/* helper modified by LLM (iteration 5): strengthened bounds and added explicit arithmetic reasoning */
proof fn lemma_arithmetic_bounds(h: i8, w: i8, h_selected: i8, w_selected: i8)
    requires
        valid_input(h as int, w as int, h_selected as int, w_selected as int),
    ensures
        (h - h_selected) >= 0,
        (w - w_selected) >= 0,
        (h - h_selected) <= 19,
        (w - w_selected) <= 19,
        (h - h_selected) as int * (w - w_selected) as int <= 361,
        (h - h_selected) as int * (w - w_selected) as int >= 0,
{
    assert(h_selected >= 1 && h_selected <= h);
    assert(w_selected >= 1 && w_selected <= w);
    assert(h <= 20 && w <= 20);
    assert(h - h_selected <= 19);
    assert(w - w_selected <= 19);
    assert(19 * 19 == 361);
    assert((h - h_selected) as int <= 19);
    assert((w - w_selected) as int <= 19);
    assert((h - h_selected) as int * (w - w_selected) as int <= 19 * 19);
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
    /* code modified by LLM (iteration 5): added proof call and overflow checks */
    proof {
        lemma_arithmetic_bounds(h, w, h_selected, w_selected);
    }
    
    let remaining_height = h - h_selected;
    let remaining_width = w - w_selected;
    
    assert(remaining_height >= 0 && remaining_width >= 0);
    assert(remaining_height <= 19 && remaining_width <= 19);
    assert((remaining_height as int) * (remaining_width as int) <= 361);
    
    let result = remaining_height * remaining_width;
    
    assert(result as int == (h - h_selected) as int * (w - w_selected) as int);
    assert(result as int == white_cells_remaining(h as int, w as int, h_selected as int, w_selected as int));
    
    result
}
// </vc-code>


}

fn main() {}