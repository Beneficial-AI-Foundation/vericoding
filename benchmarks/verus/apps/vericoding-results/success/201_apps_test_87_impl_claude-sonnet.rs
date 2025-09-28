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
/* helper modified by LLM (iteration 4): fix type annotation for seq literal */
fn get_days_in_month(m: i8) -> (result: i8)
    requires 1 <= m <= 12
    ensures result as int == days_in_month(m as int)
{
    proof {
        let ghost days = seq![31int, 28int, 31int, 30int, 31int, 30int, 31int, 31int, 30int, 31int, 30int, 31int];
        assert(days[(m - 1) as int] == days_in_month(m as int));
    }
    
    match m {
        1 => 31,
        2 => 28,
        3 => 31,
        4 => 30,
        5 => 31,
        6 => 30,
        7 => 31,
        8 => 31,
        9 => 30,
        10 => 31,
        11 => 30,
        12 => 31,
        _ => 31,
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(m: i8, d: i8) -> (result: i8)
    requires valid_input(m as int, d as int)
    ensures result as int == columns_needed(m as int, d as int) && 4 <= result as int <= 6
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use helper function to avoid ghost types in executable code */
    let month_days = get_days_in_month(m);
    let total_positions = (d - 1) + month_days;
    let columns = 1 + (total_positions - 1) / 7;
    columns as i8
}
// </vc-code>


}

fn main() {}