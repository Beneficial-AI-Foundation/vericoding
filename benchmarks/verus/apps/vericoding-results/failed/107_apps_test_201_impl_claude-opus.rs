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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut max_joy: i8 = 0;
    let mut red: i8 = 0;
    
    while red <= c / wr
        invariant
            red >= 0,
            red <= c / wr + 1,
            max_joy >= 0,
            exists|r: int, b: int| 
                0 <= r && r < red as int &&
                valid_candy_combination(r, b, c as int, wr as int, wb as int) &&
                max_joy as int == joy(r, b, hr as int, hb as int),
            forall|r: int, b: int|
                0 <= r && r < red as int &&
                valid_candy_combination(r, b, c as int, wr as int, wb as int) ==> 
                joy(r, b, hr as int, hb as int) <= max_joy as int,
        decreases c / wr - red
    {
        let blue = (c - red * wr) / wb;
        let current_joy = red * hr + blue * hb;
        
        if red == 0 {
            max_joy = current_joy;
        } else if current_joy > max_joy {
            max_joy = current_joy;
        }
        
        red = red + 1;
    }
    
    max_joy
}
// </vc-code>


}

fn main() {}