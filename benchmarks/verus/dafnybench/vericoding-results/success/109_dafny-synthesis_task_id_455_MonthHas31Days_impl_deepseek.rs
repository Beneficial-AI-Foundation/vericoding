use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn month_has_31_days_spec(month: i32) -> bool
    recommends 1 <= month <= 12
{
    month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12
}

proof fn month_has_31_days_proof(month: i32)
    requires 1 <= month <= 12
    ensures month_has_31_days_spec(month) <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
{
    match month {
        1 => assert(month_has_31_days_spec(month)),
        2 => assert(!month_has_31_days_spec(month)),
        3 => assert(month_has_31_days_spec(month)),
        4 => assert(!month_has_31_days_spec(month)),
        5 => assert(month_has_31_days_spec(month)),
        6 => assert(!month_has_31_days_spec(month)),
        7 => assert(month_has_31_days_spec(month)),
        8 => assert(month_has_31_days_spec(month)),
        9 => assert(!month_has_31_days_spec(month)),
        10 => assert(month_has_31_days_spec(month)),
        11 => assert(!month_has_31_days_spec(month)),
        12 => assert(month_has_31_days_spec(month)),
        _ => assert(false),
    }
}
// </vc-helpers>

// <vc-spec>
fn month_has_31_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
// </vc-spec>
// <vc-code>
{
    proof {
        month_has_31_days_proof(month);
    }
    if month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 {
        true
    } else {
        false
    }
}
// </vc-code>

fn main() {}

}