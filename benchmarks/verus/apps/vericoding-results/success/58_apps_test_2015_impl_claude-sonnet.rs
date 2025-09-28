// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 1 && g >= 1 && b >= 1
}

spec fn max_of_3(r: int, g: int, b: int) -> int {
    if r >= g && r >= b {
        r
    } else if g >= r && g >= b {
        g
    } else {
        b
    }
}

spec fn can_arrange(r: int, g: int, b: int) -> bool
    recommends valid_input(r, g, b)
{
    let max_count = max_of_3(r, g, b);
    let total = r + g + b;
    2 * max_count <= total + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added ghost wrapper for max computation */
proof fn lemma_max_of_3_properties(r: int, g: int, b: int)
    ensures
        max_of_3(r, g, b) >= r,
        max_of_3(r, g, b) >= g,
        max_of_3(r, g, b) >= b,
        max_of_3(r, g, b) == r || max_of_3(r, g, b) == g || max_of_3(r, g, b) == b
{
}

fn compute_max_of_3(r: i8, g: i8, b: i8) -> (result: i8)
    requires
        r >= 1,
        g >= 1,
        b >= 1
    ensures result as int == max_of_3(r as int, g as int, b as int)
{
    if r >= g && r >= b {
        r
    } else if g >= r && g >= b {
        g
    } else {
        b
    }
}

proof fn lemma_arithmetic_bounds(r: i8, g: i8, b: i8)
    requires
        r >= 1,
        g >= 1,
        b >= 1
    ensures
        r as int + g as int + b as int >= 3,
        r as int + g as int + b as int <= 3 * 127,
        max_of_3(r as int, g as int, b as int) <= 127
{
}

fn compute_arrangement_check(r: i8, g: i8, b: i8) -> (result: bool)
    requires
        r >= 1,
        g >= 1,
        b >= 1
    ensures result == can_arrange(r as int, g as int, b as int)
{
    let max_count = compute_max_of_3(r, g, b);
    
    proof {
        lemma_max_of_3_properties(r as int, g as int, b as int);
        lemma_arithmetic_bounds(r, g, b);
    }
    
    let total = r as u32 + g as u32 + b as u32;
    
    2 * (max_count as u32) <= total + 1
}
// </vc-helpers>

// <vc-spec>
fn check_lamp_arrangement(r: i8, g: i8, b: i8) -> (result: bool)
    requires valid_input(r as int, g as int, b as int)
    ensures result == can_arrange(r as int, g as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): delegate to helper function for arithmetic */
    compute_arrangement_check(r, g, b)
}
// </vc-code>


}

fn main() {}