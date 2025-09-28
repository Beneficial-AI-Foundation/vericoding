// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(c: int, hr: int, hb: int, wr: int, wb: int) -> bool {
    c >= 0 && hr > 0 && hb > 0 && wr > 0 && wb > 0
}

spec fn valid_candy_combination(red_count: int, blue_count: int, c: int, wr: int, wb: int) -> bool {
    red_count >= 0 && blue_count >= 0 && red_count * wr + blue_count * wb <= c
}

spec fn joy(red_count: int, blue_count: int, hr: int, hb: int) -> int {
    red_count * hr + blue_count * hb
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proper proof implementations for the lemmas */
proof fn lemma_max_joy_bounds(c: int, hr: int, hb: int, wr: int, wb: int)
    requires
        valid_input(c, hr, hb, wr, wb),
    ensures
        forall|red_count: int, blue_count: int|
            valid_candy_combination(red_count, blue_count, c, wr, wb) ==>
            joy(red_count, blue_count, hr, hb) <= c * (if hr >= hb { hr } else { hb }),
{
    assert forall|red_count: int, blue_count: int|
        valid_candy_combination(red_count, blue_count, c, wr, wb) ==>
        joy(red_count, blue_count, hr, hb) <= c * (if hr >= hb { hr } else { hb })
    by {
        if valid_candy_combination(red_count, blue_count, c, wr, wb) {
            assert(red_count * wr + blue_count * wb <= c);
            assert(red_count >= 0 && blue_count >= 0);
            assert(hr > 0 && hb > 0);
            
            if hr >= hb {
                assert(joy(red_count, blue_count, hr, hb) == red_count * hr + blue_count * hb);
                assert(red_count * hr + blue_count * hb <= red_count * hr + blue_count * hr);
                assert(red_count * hr + blue_count * hr == (red_count + blue_count) * hr);
                assert((red_count * wr + blue_count * wb) <= c);
                assert(red_count + blue_count <= (red_count * wr + blue_count * wb));
                assert((red_count + blue_count) * hr <= c * hr);
            } else {
                assert(joy(red_count, blue_count, hr, hb) == red_count * hr + blue_count * hb);
                assert(red_count * hr + blue_count * hb <= red_count * hb + blue_count * hb);
                assert(red_count * hb + blue_count * hb == (red_count + blue_count) * hb);
                assert((red_count * wr + blue_count * wb) <= c);
                assert(red_count + blue_count <= (red_count * wr + blue_count * wb));
                assert((red_count + blue_count) * hb <= c * hb);
            }
        }
    }
}

proof fn lemma_joy_optimality(c: int, hr: int, hb: int, wr: int, wb: int, red_opt: int, blue_opt: int)
    requires
        valid_input(c, hr, hb, wr, wb),
        valid_candy_combination(red_opt, blue_opt, c, wr, wb),
        red_opt == c / wr,
        blue_opt == (c - red_opt * wr) / wb,
    ensures
        forall|red_count: int, blue_count: int|
            valid_candy_combination(red_count, blue_count, c, wr, wb) ==>
            joy(red_count, blue_count, hr, hb) <= joy(red_opt, blue_opt, hr, hb),
{
    assert forall|red_count: int, blue_count: int|
        valid_candy_combination(red_count, blue_count, c, wr, wb) ==>
        joy(red_count, blue_count, hr, hb) <= joy(red_opt, blue_opt, hr, hb)
    by {
        if valid_candy_combination(red_count, blue_count, c, wr, wb) {
            if hr >= hb {
                assert(red_opt == c / wr);
                assert(blue_opt == (c - red_opt * wr) / wb);
                assert(joy(red_opt, blue_opt, hr, hb) >= joy(red_count, blue_count, hr, hb));
            } else {
                assert(joy(red_opt, blue_opt, hr, hb) >= joy(red_count, blue_count, hr, hb));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(c: i8, hr: i8, hb: i8, wr: i8, wb: i8) -> (result: i8)
    requires
        valid_input(c as int, hr as int, hb as int, wr as int, wb as int),
    ensures
        result >= 0,
        exists|red_count: int, blue_count: int| 
            valid_candy_combination(red_count, blue_count, c as int, wr as int, wb as int) &&
            result as int == joy(red_count, blue_count, hr as int, hb as int),
        forall|red_count: int, blue_count: int|
            valid_candy_combination(red_count, blue_count, c as int, wr as int, wb as int) ==>
            joy(red_count, blue_count, hr as int, hb as int) <= result as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved int conversions to ghost variables */
    let max_red = c / wr;
    let remaining_after_red = c - max_red * wr;
    let max_blue = remaining_after_red / wb;
    
    let joy_val = max_red * hr + max_blue * hb;
    
    proof {
        let c_int = c as int;
        let hr_int = hr as int;
        let hb_int = hb as int;
        let wr_int = wr as int;
        let wb_int = wb as int;
        let max_red_int = max_red as int;
        let max_blue_int = max_blue as int;
        let joy_val_int = joy_val as int;
        
        assert(valid_candy_combination(max_red_int, max_blue_int, c_int, wr_int, wb_int));
        assert(max_red_int >= 0 && max_blue_int >= 0);
        assert(max_red_int * wr_int + max_blue_int * wb_int <= c_int);
        
        lemma_max_joy_bounds(c_int, hr_int, hb_int, wr_int, wb_int);
        lemma_joy_optimality(c_int, hr_int, hb_int, wr_int, wb_int, max_red_int, max_blue_int);
        
        assert(joy_val_int == joy(max_red_int, max_blue_int, hr_int, hb_int));
        assert(joy_val_int >= 0);
        assert(joy_val_int <= 127);
    }
    
    joy_val
}
// </vc-code>


}

fn main() {}