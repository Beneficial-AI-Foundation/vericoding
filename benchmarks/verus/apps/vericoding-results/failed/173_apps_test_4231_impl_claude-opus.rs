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
{
    /* code modified by LLM (iteration 5): fix int usage by keeping computations in proof block */
    let remaining_h = h - h_selected;
    let remaining_w = w - w_selected;
    let result = remaining_h * remaining_w;
    
    proof {
        let remaining_h_int: int = (h as int) - (h_selected as int);
        let remaining_w_int: int = (w as int) - (w_selected as int);
        let result_int: int = remaining_h_int * remaining_w_int;
        
        assert(1 <= h_selected as int <= h as int <= 20);
        assert(1 <= w_selected as int <= w as int <= 20);
        assert(0 <= remaining_h_int <= 19);
        assert(0 <= remaining_w_int <= 19);
        assert(0 <= result_int <= 19 * 19);
        assert(result_int <= 361);
        assert(result_int <= i8::MAX as int);
        
        assert(remaining_h as int == remaining_h_int);
        assert(remaining_w as int == remaining_w_int);
        assert(result as int == result_int);
        assert(result as int == remaining_h_int * remaining_w_int);
        assert(result as int == ((h as int) - (h_selected as int)) * ((w as int) - (w_selected as int)));
        assert(result as int == white_cells_remaining(h as int, w as int, h_selected as int, w_selected as int));
        assert(result >= 0);
    }
    
    result
}
// </vc-code>


}

fn main() {}