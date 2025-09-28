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
    // Declarations
    let c_int: i32 = c as i32;
    let hr_int: i32 = hr as i32;
    let hb_int: i32 = hb as i32;
    let wr_int: i32 = wr as i32;
    let wb_int: i32 = wb as i32;
    let mut max_j: i32 = 0;
    let max_r: i32 = if wr_int > 0 { c_int / wr_int } else { 0 };
    let max_b: i32 = if wb_int > 0 { c_int / wb_int } else { 0 };
    let mut r: i32 = 0;
    while r <= max_r
        decreases max_r - r
    {
        let mut b: i32 = 0;
        while b <= max_b
            decreases max_b - b
        {
            let cost = r as i64 * wr_int as i64 + b as i64 * wb_int as i64;
            if cost <= c_int as i64 {
                let j = r as i64 * hr_int as i64 + b as i64 * hb_int as i64;
                if j > max_j as i64 {
                    max_j = j as i32;
                }
            }
            b += 1;
        }
        r += 1;
    }
    let result = max_j as i8;
    result
}
// </vc-code>


}

fn main() {}