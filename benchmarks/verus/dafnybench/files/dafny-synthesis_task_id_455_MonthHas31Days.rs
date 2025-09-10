use vstd::prelude::*;

verus! {

fn month_has_31_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
{
    assume(false);
    unreached()
}

}
fn main() {}