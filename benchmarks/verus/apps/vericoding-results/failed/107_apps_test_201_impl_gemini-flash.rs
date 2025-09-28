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
/* helper modified by LLM (iteration 5): This section is intentionally left blank. */
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
    /* code modified by LLM (iteration 5): Corrected type casting in loop conditions and variable assignments to conform with Verus's ghost type usage rules. */
    let ghost c_int = c as int;
    let ghost hr_int = hr as int;
    let ghost hb_int = hb as int;
    let ghost wr_int = wr as int;
    let ghost wb_int = wb as int;

    let mut max_joy: i8 = 0;

    let mut red_count: i8 = 0;
    while (red_count as int) * wr_int <= c_int
        invariant 
            red_count >= 0,
            max_joy >= 0,
            (red_count as int) * wr_int <= c_int,
            forall|r: int, b: int|
                #![auto]
                (r >= 0 && b >= 0 && r * wr_int + b * wb_int <= c_int && (r < red_count as int || (r == red_count as int && b < 0)))
                ==>
                joy(r, b, hr_int, hb_int) <= max_joy as int,
        decreases c_int / wr_int - (red_count as int)
    {
        let ghost remaining_capacity = c_int - (red_count as int) * wr_int;
        let mut blue_count: i8 = 0;
        while (blue_count as int) * wb_int <= remaining_capacity
            invariant 
                blue_count >= 0,
                red_count >= 0,
                remaining_capacity >= 0,
                max_joy >= 0,
                (blue_count as int) * wb_int <= remaining_capacity,
                forall|r: int, b: int|
                    #![auto]
                    (r >= 0 && b >= 0 && r * wr_int + b * wb_int <= c_int && (r < red_count as int || (r == red_count as int && b < blue_count as int)))
                    ==>
                    joy(r, b, hr_int, hb_int) <= max_joy as int,
            decreases remaining_capacity / wb_int - (blue_count as int)
        {
            let ghost current_joy_val = joy(red_count as int, blue_count as int, hr_int, hb_int);
            if current_joy_val > max_joy as int {
                max_joy = current_joy_val.try_into().unwrap();
            }
            blue_count = blue_count + 1;
        }
        red_count = red_count + 1;
    }
    max_joy
}
// </vc-code>


}

fn main() {}