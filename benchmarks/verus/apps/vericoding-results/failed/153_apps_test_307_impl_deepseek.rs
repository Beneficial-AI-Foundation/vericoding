// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k2: int, k3: int, k5: int, k6: int) -> bool {
    k2 >= 0 && k3 >= 0 && k5 >= 0 && k6 >= 0 &&
    k2 <= 5000000 && k3 <= 5000000 && k5 <= 5000000 && k6 <= 5000000
}

spec fn optimal_sum(k2: int, k3: int, k5: int, k6: int) -> int
    recommends valid_input(k2, k3, k5, k6)
{
    let count256 = if k2 <= k5 { if k2 <= k6 { k2 } else { k6 } } else { if k5 <= k6 { k5 } else { k6 } };
    let remaining_k2 = k2 - count256;
    let count32 = if k3 <= remaining_k2 { k3 } else { remaining_k2 };
    256 * count256 + 32 * count32
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert min3 to regular function with proper spec */
fn min3(a: i8, b: i8, c: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0,
        c >= 0,
    ensures
        result <= a,
        result <= b,
        result <= c
{
    if a <= b {
        if a <= c { a } else { c }
    } else {
        if b <= c { b } else { c }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(k2: i8, k3: i8, k5: i8, k6: i8) -> (result: i8)
    requires 
        valid_input(k2 as int, k3 as int, k5 as int, k6 as int)
    ensures 
        result >= 0,
        result as int == optimal_sum(k2 as int, k3 as int, k5 as int, k6 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use regular function min3 instead of spec function */
{
    let count256 = min3(k2, k5, k6);
    let remaining_k2 = k2 - count256;
    let count32 = if k3 <= remaining_k2 { k3 } else { remaining_k2 };
    
    // Convert to int to avoid overflow during multiplication
    let total_int = 256 * (count256 as i32) + 32 * (count32 as i32);
    
    // Verify the result is within i8 range
    proof {
        assert(total_int >= 0);
        assert(total_int <= 127);
    }
    
    total_int as i8
}
// </vc-code>


}

fn main() {}