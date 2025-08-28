use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was a syntax error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_month_with_30_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 4 || month == 6 || month == 9 || month == 11)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_month_with_30_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 4 || month == 6 || month == 9 || month == 11)
{
    let result = (month == 4 || month == 6 || month == 9 || month == 11);
    result
}
// </vc-code>

fn main() {
}

}