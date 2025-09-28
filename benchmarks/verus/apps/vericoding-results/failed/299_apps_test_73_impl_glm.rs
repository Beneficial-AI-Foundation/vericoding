// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn compute_position(days: int, v0: int, v1: int, a: int, l: int) -> int
    decreases days
{
    if days <= 0 {
        0
    } else {
        let prev_pos = compute_position(days - 1, v0, v1, a, l);
        let after_reread = if prev_pos - l > 0 { prev_pos - l } else { 0 };
        let read_today = if v1 < v0 + a * (days - 1) { v1 } else { v0 + a * (days - 1) };
        after_reread + read_today
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(c: u8, v0: u8, v1: u8, a: u8, l: u8) -> (result: u8)
    requires
        1 <= c && c <= 100,
        0 <= l && l < v0 && v0 <= v1 && v1 <= 100,
        0 <= a && a <= 100
    ensures
        result >= 1,
        compute_position(result as int, v0 as int, v1 as int, a as int, l as int) >= c as int,
        forall|days: int| 1 <= days && days < result as int ==> compute_position(days, v0 as int, v1 as int, a as int, l as int) < c as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed RangeInclusive to Range for Verus compatibility */
    let mut current_pos: u16 = 0;

    for day in 1u8..101u8 {
        current_pos = if current_pos > l as u16 { current_pos - l as u16 } else { 0 };

        let d_minus_1 = (day - 1) as u16;
        let threshold = (v0 as u16) + (a as u16) * d_minus_1;
        let reading = if (v1 as u16) < threshold {
            v1 as u16
        } else {
            threshold
        };

        current_pos += reading;

        if current_pos >= c as u16 {
            return day;
        }
    }

    return 100u8;
}
// </vc-code>


}

fn main() {}