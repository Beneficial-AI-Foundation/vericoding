// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_day(day: &str) -> bool {
    day == "SUN" || day == "MON" || day == "TUE" || day == "WED" || day == "THU" || day == "FRI" || day == "SAT"
}

spec fn days_until_sunday(day: &str) -> int {
    if day == "SUN" { 7 }
    else if day == "MON" { 6 }
    else if day == "TUE" { 5 }
    else if day == "WED" { 4 }
    else if day == "THU" { 3 }
    else if day == "FRI" { 2 }
    else { 1 }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_days_until_sunday_nonzero(day: &str)
    requires valid_day(day)
    ensures days_until_sunday(day) >= 1 && days_until_sunday(day) <= 7
{
    /* helper modified by LLM (iteration 2): remove verification bypass and use proper proof */
    reveal(days_until_sunday);
    assert(day == "SUN" || day == "MON" || day == "TUE" || day == "WED" || day == "THU" || day == "FRI" || day == "SAT") by {
        assert(valid_day(day));
    }
    if day == "SUN" {
        assert(days_until_sunday(day) == 7);
    } else if day == "MON" {
        assert(days_until_sunday(day) == 6);
    } else if day == "TUE" {
        assert(days_until_sunday(day) == 5);
    } else if day == "WED" {
        assert(days_until_sunday(day) == 4);
    } else if day == "THU" {
        assert(days_until_sunday(day) == 3);
    } else if day == "FRI" {
        assert(days_until_sunday(day) == 2);
    } else {
        assert(days_until_sunday(day) == 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn days_to_next_sunday(day: &str) -> (result: i8)
    requires 
        valid_day(day)
    ensures 
        result as int >= 1 && result as int <= 7,
        result as int == days_until_sunday(day)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): remove verification bypass and use lemma */
    proof { lemma_days_until_sunday_nonzero(day); }
    
    match day {
        "SUN" => 7,
        "MON" => 6,
        "TUE" => 5,
        "WED" => 4,
        "THU" => 3,
        "FRI" => 2,
        "SAT" => 1,
        _ => unreached(),
    }
}
// </vc-code>


}

fn main() {}