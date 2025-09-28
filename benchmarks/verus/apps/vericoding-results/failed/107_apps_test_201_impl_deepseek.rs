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
/* helper modified by LLM (iteration 5): fixed lemma declaration with ! */
lemma max_joy_exists!(c: int, hr: int, hb: int, wr: int, wb: int)
    requires
        valid_input(c, hr, hb, wr, wb),
    ensures
        exists|red_count: int, blue_count: int|
            valid_candy_combination(red_count, blue_count, c, wr, wb),
        exists|red_count: int, blue_count: int|
            valid_candy_combination(red_count, blue_count, c, wr, wb) &&
            forall|r: int, b: int| #![trigger joy(r, b, hr, hb)]
                valid_candy_combination(r, b, c, wr, wb) ==>
                joy(r, b, hr, hb) <= joy(red_count, blue_count, hr, hb),
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
    /* code modified by LLM (iteration 5): fixed lemma call syntax with ! */
    proof {
        max_joy_exists!(c as int, hr as int, hb as int, wr as int, wb as int);
    }
    let max_r = (c as int / wr as int) as i8;
    let mut max_joy = 0i8;
    let mut red_count: i8 = 0;
    while red_count <= max_r
        invariant
            red_count >= 0,
            red_count <= max_r + 1,
            exists|blue_count: int| valid_candy_combination(red_count as int, blue_count, c as int, wr as int, wb as int),
            forall|r: int, b: int| #![trigger joy(r, b, hr as int, hb as int)]
                (r >= 0 && r < red_count as int && valid_candy_combination(r, b, c as int, wr as int, wb as int)) ==>
                joy(r, b, hr as int, hb as int) <= max_joy as int,
        decreases (max_r as int - red_count as int),
    {
        let rem = c - red_count * wr;
        if rem >= 0 {
            let blue_count = rem / wb;
            let current_joy = red_count * hr + blue_count * hb;
            if current_joy > max_joy {
                max_joy = current_joy;
            }
        }
        red_count = red_count + 1;
    }
    max_joy
}
// </vc-code>


}

fn main() {}