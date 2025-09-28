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
proof fn lemma_compute_position_monotonic(days1: int, days2: int, v0: int, v1: int, a: int, l: int)
    requires
        days1 <= days2,
        v0 >= 0,
        v1 >= v0,
        a >= 0,
        l >= 0,
        l < v0
    ensures
        compute_position(days1, v0, v1, a, l) <= compute_position(days2, v0, v1, a, l)
    decreases days2 - days1
{
    if days1 < days2 {
        lemma_compute_position_monotonic(days1, days2 - 1, v0, v1, a, l);
    }
}

proof fn lemma_compute_position_positive(days: int, v0: int, v1: int, a: int, l: int)
    requires
        days >= 0,
        v0 >= 0,
        v1 >= v0,
        a >= 0,
        l >= 0,
        l < v0
    ensures
        compute_position(days, v0, v1, a, l) >= 0
    decreases days
{
    if days > 0 {
        lemma_compute_position_positive(days - 1, v0, v1, a, l);
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
    /* code modified by LLM (iteration 5): Fix variable declaration syntax */
    let mut days: u8 = 1;
    
    {  // Remove ghost block from implementation code
        let c_int = c as int;
        let v0_int = v0 as int;
        let v1_int = v1 as int;
        let a_int = a as int;
        let l_int = l as int;
    }
    
    while compute_position(days as int, v0 as int, v1 as int, a as int, l as int) < c as int
        invariant
            1 <= days,
            compute_position(days as int, v0 as int, v1 as int, a as int, l as int) >= 0,
            forall|d: int| 1 <= d && d < days as int ==> compute_position(d, v0 as int, v1 as int, a as int, l as int) < c as int
        decreases 100 - days
    {
        days = days + 1;
        proof {
            let v0_int = v0 as int;
            let v1_int = v1 as int;
            let a_int = a as int;
            let l_int = l as int;
            lemma_compute_position_monotonic((days - 1) as int, days as int, v0_int, v1_int, a_int, l_int);
            lemma_compute_position_positive(days as int, v0_int, v1_int, a_int, l_int);
        }
    }
    
    days
}
// </vc-code>


}

fn main() {}