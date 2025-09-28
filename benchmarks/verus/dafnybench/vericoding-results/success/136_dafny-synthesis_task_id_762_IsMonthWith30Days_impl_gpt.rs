use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_month_with_30_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 4 || month == 6 || month == 9 || month == 11)
// </vc-spec>
// <vc-code>
{
    month == 4 || month == 6 || month == 9 || month == 11
}
// </vc-code>

fn main() {
}

}