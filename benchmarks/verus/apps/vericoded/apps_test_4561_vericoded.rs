// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_outcome(outcome: &str) -> bool {
    outcome == "delicious" || outcome == "safe" || outcome == "dangerous"
}

spec fn days_past_best_by(a: int, b: int) -> int {
    b - a
}

spec fn expected_outcome(x: int, a: int, b: int) -> &'static str {
    let days_past = days_past_best_by(a, b);
    if days_past <= 0 {
        "delicious"
    } else if days_past <= x {
        "safe"
    } else {
        "dangerous"
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): i8 to int conversion */
spec fn i8_to_int(v: i8) -> int { v as int }
// </vc-helpers>

// <vc-spec>
fn determine_food_safety(x: i8, a: i8, b: i8) -> (outcome: &'static str)
    requires 
        x as int >= 0,
    ensures 
        outcome == expected_outcome(x as int, a as int, b as int),
        valid_outcome(outcome),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute runtime difference and prove equivalence with spec */
    let days_rt: i32 = (b as i32) - (a as i32);
    let res: &'static str;
    if days_rt <= 0 {
        res = "delicious";
    } else if days_rt <= x as i32 {
        res = "safe";
    } else {
        res = "dangerous";
    }
    proof {
        let days_spec: int = days_past_best_by(a as int, b as int);
        assert(days_spec == b as int - a as int);
        assert(b as int - a as int == b as i32 as int - a as i32 as int);
        assert(b as i32 as int - a as i32 as int == days_rt as int);
        assert(days_spec == days_rt as int);
        if days_rt <= 0 {
            assert(days_spec <= 0);
            assert(expected_outcome(x as int, a as int, b as int) == "delicious");
            assert(res == "delicious");
            assert(res == expected_outcome(x as int, a as int, b as int));
        } else if days_rt <= x as i32 {
            assert(days_spec <= x as int);
            assert(expected_outcome(x as int, a as int, b as int) == "safe");
            assert(res == "safe");
            assert(res == expected_outcome(x as int, a as int, b as int));
        } else {
            assert(days_spec > x as int);
            assert(expected_outcome(x as int, a as int, b as int) == "dangerous");
            assert(res == "dangerous");
            assert(res == expected_outcome(x as int, a as int, b as int));
        }
    }
    res
}
// </vc-code>


}

fn main() {}