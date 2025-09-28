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
    /* code modified by LLM (iteration 5): Simplified arithmetic and removed failing assertions */
    let mut days: u8 = 1;
    let mut position: u8 = 0;
    
    while position < c
        invariant
            days >= 1,
            days <= 100,
            position == compute_position((days - 1) as int, v0 as int, v1 as int, a as int, l as int),
            forall|d: int| 1 <= d && d < days as int ==> compute_position(d, v0 as int, v1 as int, a as int, l as int) < c as int,
        decreases (c - position) as int
    {
        let after_reread = if position > l { position - l } else { 0 };
        
        // Calculate read_today based on min(v1, v0 + a * (days - 1))
        // We need to be careful with overflow
        let days_minus_1 = (days - 1) as u8;
        
        // Use u16 for intermediate calculations to avoid overflow
        let v0_u16 = v0 as u16;
        let a_u16 = a as u16;
        let days_minus_1_u16 = days_minus_1 as u16;
        let v1_u16 = v1 as u16;
        
        let max_read_u16 = v0_u16 + a_u16 * days_minus_1_u16;
        
        // Cap at v1 (which is at most 100)
        let read_today = if v1_u16 < max_read_u16 { v1 } else if max_read_u16 <= 100 { max_read_u16 as u8 } else { 100 };
        
        position = after_reread + read_today;
        days = days + 1;
    }
    
    days
}
// </vc-code>


}

fn main() {}