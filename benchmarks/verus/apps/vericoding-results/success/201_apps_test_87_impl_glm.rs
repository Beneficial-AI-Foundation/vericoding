// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(m: int, d: int) -> bool {
    1 <= m <= 12 && 1 <= d <= 7
}

spec fn days_in_month(m: int) -> int {
    if 1 <= m <= 12 {
        seq![31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1]
    } else {
        0
    }
}

spec fn columns_needed(m: int, d: int) -> int {
    if valid_input(m, d) {
        1 + (d - 1 + days_in_month(m) - 1) / 7
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
fn days_in_month_impl(m: i8) -> (days: i8)
    requires 1 <= m as int <= 12
    ensures days as int == days_in_month(m as int)
{
    let month_days = [
        31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31
    ];
    month_days[(m - 1) as usize]
}
// </vc-helpers>

// <vc-spec>
fn solve(m: i8, d: i8) -> (result: i8)
    requires valid_input(m as int, d as int)
    ensures result as int == columns_needed(m as int, d as int) && 4 <= result as int <= 6
// </vc-spec>
// <vc-code>
{
    let days = days_in_month_impl(m);
    let offset = d - 1;
    let total_days = offset + days;
    let columns = 1 + (total_days - 1) / 7;
    columns
}
// </vc-code>


}

fn main() {}