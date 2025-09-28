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
/* helper modified by LLM (iteration 5): relate compute_position(days + 1) to compute_position(days) */
spec fn compute_position_step(days: int, v0: int, v1: int, a: int, l: int)
    requires
        days >= 1,
    ensures
        compute_position(days + 1, v0, v1, a, l) == {
            let prev = compute_position(days, v0, v1, a, l);
            let after = if prev - l > 0 { prev - l } else { 0 };
            let read = if v1 < v0 + a * days { v1 } else { v0 + a * days };
            after + read
        },
{
    proof {
        reveal(compute_position);
        assert(compute_position(days + 1, v0, v1, a, l) == {
            let prev = compute_position(days, v0, v1, a, l);
            let after = if prev - l > 0 { prev - l } else { 0 };
            let read = if v1 < v0 + a * days { v1 } else { v0 + a * days };
            after + read
        });
    }
}

/* helper modified by LLM (iteration 5): base case compute_position(1) == v0 when v0 <= v1 */
spec fn compute_position_one(v0: int, v1: int, a: int, l: int)
    requires
        v0 <= v1,
    ensures
        compute_position(1, v0, v1, a, l) == v0,
{
    proof {
        reveal(compute_position);
        assert(compute_position(1, v0, v1, a, l) == {
            let prev = compute_position(0, v0, v1, a, l);
            let after = if prev - l > 0 { prev - l } else { 0 };
            let read = if v1 < v0 + a * 0 { v1 } else { v0 + a * 0 };
            after + read
        });
        assert(compute_position(0, v0, v1, a, l) == 0);
        assert((v0 + a * 0) == v0);
        assert((if v1 < v0 { v1 } else { v0 }) == v0);
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
    /* code modified by LLM (iteration 5): corrected loop invariant and day-step calculation matching spec */
    let mut days: u8 = 1;
    let mut pos: u8 = v0;

    while pos < c
        invariant
            days as int >= 1,
            pos as int == compute_position(days as int, v0 as int, v1 as int, a as int, l as int),
            forall|i: int| 1 <= i && i < days as int ==> compute_position(i, v0 as int, v1 as int, a as int, l as int) < c as int,
        decreases
            (c as int) - (pos as int)
    {
        let after: u8 = if pos > l { pos - l } else { 0 };
        let accel32: u32 = (v0 as u32) + (a as u32) * (days as u32);
        let read_today: u8 = if (v1 as u32) < accel32 { v1 } else { accel32 as u8 };
        let next_pos: u8 = after + read_today;

        proof {
            reveal(compute_position);
            compute_position_step(days as int, v0 as int, v1 as int, a as int, l as int);
            let prev_pos_int: int = compute_position(days as int, v0 as int, v1 as int, a as int, l as int);
            let after_i: int = if prev_pos_int - (l as int) > 0 { prev_pos_int - (l as int) } else { 0 };
            let read_i: int = if (v1 as int) < (v0 as int) + (a as int) * (days as int) { v1 as int } else { (v0 as int) + (a as int) * (days as int) };
            assert(after_i == (after as int));
            assert(read_i == (read_today as int));
            assert((next_pos as int) == after_i + read_i);
            assert(compute_position(days as int + 1, v0 as int, v1 as int, a as int, l as int) == after_i + read_i);
        }

        if next_pos >= c {
            proof {
                assert((next_pos as int) == compute_position(days as int + 1, v0 as int, v1 as int, a as int, l as int));
                assert((next_pos as int) >= (c as int));
            }
            return (days + 1) as u8;
        }

        pos = next_pos;
        days = days + 1;
    }

    proof {
        assert((pos as int) == compute_position(days as int, v0 as int, v1 as int, a as int, l as int));
        assert((pos as int) >= (c as int));
    }

    days as u8
}

// </vc-code>


}

fn main() {}