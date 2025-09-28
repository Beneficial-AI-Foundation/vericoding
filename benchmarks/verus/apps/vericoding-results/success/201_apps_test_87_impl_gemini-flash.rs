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
/* helper modified by LLM (iteration 5): This section is intentionally left empty as no helpers are needed to fix the current error. */
// </vc-helpers>

// <vc-spec>
fn solve(m: i8, d: i8) -> (result: i8)
    requires valid_input(m as int, d as int)
    ensures result as int == columns_needed(m as int, d as int) && 4 <= result as int <= 6
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The `seq` data type (`vstd::seq::Seq`) cannot be indexed directly in executable code. Changed `seq!` to a `Vec` array to allow direct indexing for `days_in_month` calculations. */
    let month_val: i8 = m;
    let day_val: i8 = d;

    let dim_val: u8;
    if 1 <= month_val && month_val <= 12 {
        let days_in_month_array = [31u8, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
        dim_val = days_in_month_array[(month_val - 1) as usize];
    } else {
        dim_val = 0;
    }

    let num_columns_val = 1 + (day_val - 1 + dim_val as i8 - 1) / 7;

    proof {
        assert(dim_val as int == days_in_month(month_val as int));
        assert(num_columns_val as int == columns_needed(m as int, d as int));
    }

    num_columns_val
}
// </vc-code>


}

fn main() {}