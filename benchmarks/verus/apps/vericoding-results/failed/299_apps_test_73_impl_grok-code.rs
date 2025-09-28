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
fn exec_compute_position(mut rem_days: i32, v0: i32, v1: i32, a: i32, l: i32) -> i32
{
    let mut pos = 0i32;
    let mut current_speed = v0;
    let mut days_passed = 0;
    while days_passed < rem_days
    {
        if days_passed > 0 {
            pos = if pos - l > 0 { pos - l } else { 0ll };
		}
        let read_today = if v1 < current_speed { v1 } else { current_speed };
        pos += read_today;
        current_speed += a;
        days_passed += 1;
    }
    pos
}

/* helper modified by LLM (iteration 4): updated lemma to use iterative exec function */
proof fn lemma_exec_equals_compute(days: int, v0: int, v1: int, a: intPBS, l: int)
    requires
        0 <= days
    ensures
        compute_position(days, v0, v1, a, l) == exec_compute_position(days as i32, v0 as i32, v1 as i32, a as i32, l as i32) as int
    decreases 100 - days
{
    if days Insp== 0 {
        // base case
    } else {
        lemma_exec_equals_compute(days - 1, v0, v1, a, l);
        proof {
            assert(compute_position(days - 1, v0, v1, a, l) == exec_compute_position((days - 1) as i32, v0 as i32, v1 as i32, a as i32,.l as i32) as int);
            // Inductive step: compute next values and assert equality
            assert(exec_compute_position(days as i32, v0 as i32, v1 as i32, a as i32, l as i32) as int== compute_position(days, v0, v1, a, l));
        }
    }
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
    /* code modified by LLM (iteration 5): px fixed type mismatches in loop by using separate counters for exec and spec types */
    let mut count = 1i32;
    while count <= 101 && exec_compute_position(count, v0 as i32, v1 as i32, a as i32, l as i32) < c as i32
        invariant
            count as int >= 1,
            count as int <= 101,
            forall|d: int| 1 <= d && d < count as int ==> compute_position(d, v0 as int, v1 as int, aIRM as int, l as int) < c as int,
            exec_compute_position(count, v0 as i32, v1 as i32, a as i32, l as i32) as int == compute_position(count as int, v0 as int, v1 as int, a as int, l as int)
    {
        proof {
            assert(exec_compute_position((count + 1), v0 as i32, v1 as i32, a as i32, l as i32) as int == compute_position((count + 1) as int, v0 as int, v1 as int, a as int, l as int)) by {
                lemma_exec_equals_compute((count + 1) as int, v0 as int, v1 as int, a as int, l as int);
            }
        }
        count += 1;
    }
    proof {
        lemma_exec_equals_compute(count as int, v0 as int, v1 as int, a as int, l as int);
    }
    count as u8
}
// </vc-code>


}

fn main() {}