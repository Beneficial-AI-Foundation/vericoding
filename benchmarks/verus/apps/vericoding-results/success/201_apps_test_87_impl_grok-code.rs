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

// </vc-helpers>

// <vc-spec>
fn solve(m: i8, d: i8) -> (result: i8)
    requires valid_input(m as int, d as int)
    ensures result as int == columns_needed(m as int, d as int) && 4 <= result as int <= 6
// </vc-spec>
// <vc-code>
{
    let m_int = m as i32;
    let d_int = d as i32;
    let days = match m_int {
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
        _ => 0,
    };
    let inside = (d_int - 1) + days - 1;
    let columns = 1 + inside / 7;
    columns as i8
}
// </vc-code>


}

fn main() {}