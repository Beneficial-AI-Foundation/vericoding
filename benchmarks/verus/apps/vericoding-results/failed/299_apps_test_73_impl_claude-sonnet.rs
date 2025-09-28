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
/* helper modified by LLM (iteration 5): fixed lemma proofs with proper induction and arithmetic reasoning */
proof fn lemma_compute_position_monotonic(days1: int, days2: int, v0: int, v1: int, a: int, l: int)
    requires
        0 <= days1 <= days2,
        0 <= l < v0 <= v1,
        0 <= a
    ensures
        compute_position(days1, v0, v1, a, l) <= compute_position(days2, v0, v1, a, l)
    decreases days2
{
    if days1 == days2 {
        return;
    }
    if days2 <= 0 {
        return;
    }
    if days1 <= 0 {
        lemma_compute_position_nonnegative(days2, v0, v1, a, l);
        return;
    }
    lemma_compute_position_monotonic(days1 - 1, days2 - 1, v0, v1, a, l);
    lemma_compute_position_monotonic(days1, days2 - 1, v0, v1, a, l);
    
    let pos_prev = compute_position(days2 - 1, v0, v1, a, l);
    let after_reread = if pos_prev - l > 0 { pos_prev - l } else { 0 };
    let read_today = if v1 < v0 + a * (days2 - 1) { v1 } else { v0 + a * (days2 - 1) };
    
    assert(after_reread >= 0);
    assert(read_today >= 0);
    assert(compute_position(days2, v0, v1, a, l) == after_reread + read_today);
}

proof fn lemma_compute_position_nonnegative(days: int, v0: int, v1: int, a: int, l: int)
    requires
        0 <= l < v0 <= v1,
        0 <= a
    ensures
        compute_position(days, v0, v1, a, l) >= 0
    decreases days
{
    if days <= 0 {
        return;
    }
    lemma_compute_position_nonnegative(days - 1, v0, v1, a, l);
    
    let prev_pos = compute_position(days - 1, v0, v1, a, l);
    let after_reread = if prev_pos - l > 0 { prev_pos - l } else { 0 };
    let read_today = if v1 < v0 + a * (days - 1) { v1 } else { v0 + a * (days - 1) };
    
    assert(after_reread >= 0);
    assert(read_today >= v0);
    assert(v0 > 0);
    assert(after_reread + read_today >= 0);
}

proof fn lemma_compute_position_bounds(days: int, v0: int, v1: int, a: int, l: int)
    requires
        days >= 1,
        0 <= l < v0 <= v1,
        0 <= a
    ensures
        compute_position(days, v0, v1, a, l) <= days * v1
    decreases days
{
    if days == 1 {
        let read_today = if v1 < v0 + a * 0 { v1 } else { v0 + a * 0 };
        assert(read_today == if v1 < v0 { v1 } else { v0 });
        assert(read_today <= v1);
        assert(compute_position(1, v0, v1, a, l) == read_today);
        return;
    }
    
    lemma_compute_position_bounds(days - 1, v0, v1, a, l);
    
    let prev_pos = compute_position(days - 1, v0, v1, a, l);
    let after_reread = if prev_pos - l > 0 { prev_pos - l } else { 0 };
    let read_today = if v1 < v0 + a * (days - 1) { v1 } else { v0 + a * (days - 1) };
    
    assert(prev_pos <= (days - 1) * v1);
    assert(after_reread <= prev_pos);
    assert(read_today <= v1);
    assert(compute_position(days, v0, v1, a, l) == after_reread + read_today);
    assert(after_reread + read_today <= prev_pos + v1);
    assert(prev_pos + v1 <= (days - 1) * v1 + v1);
    assert((days - 1) * v1 + v1 == days * v1);
}
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
    /* code modified by LLM (iteration 5): fixed syntax error with conditional expression */
    let mut day = 1u8;
    
    while day < 255
        invariant
            1 <= day <= 255,
            day <= v0 || day <= v1,
            forall|d: int| 1 <= d && d < day as int ==> compute_position(d, v0 as int, v1 as int, a as int, l as int) < c as int
        decreases 255 - day
    {
        if day as int <= 255 / (v1 as int) {
            proof {
                lemma_compute_position_nonnegative(day as int, v0 as int, v1 as int, a as int, l as int);
                lemma_compute_position_bounds(day as int, v0 as int, v1 as int, a as int, l as int);
            }
            
            let mut pos = 0;
            let mut current_day = 1;
            
            while current_day <= day as int
                invariant
                    1 <= current_day <= day as int + 1,
                    1 <= day <= 255,
                    0 <= pos
                decreases day as int - current_day
            {
                if current_day > 1 {
                    if pos > l as int {
                        pos = pos - l as int;
                    } else {
                        pos = 0;
                    }
                }
                
                let max_speed = v0 as int + a as int * (current_day - 1);
                let read_today = if v1 as int < max_speed {
                    v1 as int
                } else {
                    max_speed
                };
                
                pos = pos + read_today;
                current_day = current_day + 1;
            }
            
            if pos >= c as int {
                return day;
            }
        }
        
        day = day + 1;
    }
    
    255
}
// </vc-code>


}

fn main() {}