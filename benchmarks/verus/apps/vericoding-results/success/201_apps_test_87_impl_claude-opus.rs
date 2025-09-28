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
    /* code modified by LLM (iteration 2): fixed type annotation for integer literal */
    let days = if m == 1 { 31 }
        else if m == 2 { 28 }
        else if m == 3 { 31 }
        else if m == 4 { 30 }
        else if m == 5 { 31 }
        else if m == 6 { 30 }
        else if m == 7 { 31 }
        else if m == 8 { 31 }
        else if m == 9 { 30 }
        else if m == 10 { 31 }
        else if m == 11 { 30 }
        else { 31 };
    
    assert(days == days_in_month(m as int));
    
    let result = 1 + (d - 1 + days - 1) / 7;
    
    assert(result as int == columns_needed(m as int, d as int));
    assert(4 <= result as int <= 6) by {
        assert(1 <= d <= 7);
        assert(28 <= days <= 31);
        assert(d - 1 + days - 1 <= 6 + 31 - 1);
        assert(d - 1 + days - 1 <= 36);
        assert((d - 1 + days - 1) / 7 <= 36int / 7);
        assert((d - 1 + days - 1) / 7 <= 5);
        assert(result <= 6);
        
        assert(d - 1 + days - 1 >= 0 + 28 - 1);
        assert(d - 1 + days - 1 >= 27);
        assert((d - 1 + days - 1) / 7 >= 27int / 7);
        assert((d - 1 + days - 1) / 7 >= 3);
        assert(result >= 4);
    }
    
    result
}
// </vc-code>


}

fn main() {}