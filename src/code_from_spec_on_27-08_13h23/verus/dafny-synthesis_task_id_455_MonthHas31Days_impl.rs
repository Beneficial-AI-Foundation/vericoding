use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn month_has_31_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn month_has_31_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
{
    month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12
}
// </vc-code>

fn main() {}

}