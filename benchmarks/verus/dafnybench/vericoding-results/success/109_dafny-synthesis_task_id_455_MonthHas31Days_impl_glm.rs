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
    if month == 1 {
        true
    } else if month == 3 {
        true
    } else if month == 5 {
        true
    } else if month == 7 {
        true
    } else if month == 8 {
        true
    } else if month == 10 {
        true
    } else if month == 12 {
        true
    } else {
        false
    }
}
// </vc-code>

fn main() {}

}