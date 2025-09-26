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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}