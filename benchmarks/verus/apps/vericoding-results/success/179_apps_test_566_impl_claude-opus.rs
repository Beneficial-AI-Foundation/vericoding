// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 0 && g >= 0 && b >= 0
}

spec fn max_tables(r: int, g: int, b: int) -> int
    recommends valid_input(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8, b: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int, b as int)
    ensures 
        result as int == max_tables(r as int, g as int, b as int),
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added overflow prevention with proper bounds checking */
    // Since r, g, b are all non-negative i8 values, their sum could overflow i8
    // We need to compute in a way that avoids overflow
    
    // First, let's use i32 for intermediate computations to avoid overflow
    let r32 = r as i32;
    let g32 = g as i32;
    let b32 = b as i32;
    
    let sum32 = r32 + g32 + b32;
    let sum_div_3_32 = sum32 / 3;
    
    let rg32 = r32 + g32;
    let rb32 = r32 + b32;
    let gb32 = g32 + b32;
    
    let min_rg_rb32 = if rg32 <= rb32 { rg32 } else { rb32 };
    let min_gb_above32 = if gb32 <= min_rg_rb32 { gb32 } else { min_rg_rb32 };
    let result32 = if sum_div_3_32 <= min_gb_above32 { sum_div_3_32 } else { min_gb_above32 };
    
    // The result should fit in i8 since it's at most the sum of two values
    let result = result32 as i8;
    
    proof {
        let r_int = r as int;
        let g_int = g as int;
        let b_int = b as int;
        
        assert(r32 as int == r_int);
        assert(g32 as int == g_int);
        assert(b32 as int == b_int);
        assert(sum32 as int == r_int + g_int + b_int);
        assert(sum_div_3_32 as int == (r_int + g_int + b_int) / 3);
        assert(rg32 as int == r_int + g_int);
        assert(rb32 as int == r_int + b_int);
        assert(gb32 as int == g_int + b_int);
        assert(min_rg_rb32 as int == min(rg32 as int, rb32 as int));
        assert(min_gb_above32 as int == min(gb32 as int, min_rg_rb32 as int));
        assert(result32 as int == min(sum_div_3_32 as int, min_gb_above32 as int));
        assert(result32 as int == min(min(sum32 as int / 3, gb32 as int), min(rg32 as int, rb32 as int)));
        assert(result32 as int == min(min(min((r_int + g_int + b_int) / 3, r_int + g_int), r_int + b_int), g_int + b_int));
        assert(result32 as int == max_tables(r_int, g_int, b_int));
        assert(result as int == result32 as int);
        assert(result as int == max_tables(r_int, g_int, b_int));
        assert(result >= 0);
    }
    
    result
}
// </vc-code>


}

fn main() {}