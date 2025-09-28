use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn month_has_31_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
// </vc-spec>
// <vc-code>
{
    // Months with 31 days: January (1), March (3), May (5), July (7), August (8), October (10), December (12)
    let has_31_days = month == 1
        || month == 3
        || month == 5
        || month == 7
        || month == 8
        || month == 10
        || month == 12;

    has_31_days
}
// </vc-code>

fn main() {}

}