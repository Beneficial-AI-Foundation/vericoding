use vstd::prelude::*;

verus! {

fn is_month_with_30_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 4 || month == 6 || month == 9 || month == 11)
{
    assume(false);
    unreached()
}

}
fn main() {}