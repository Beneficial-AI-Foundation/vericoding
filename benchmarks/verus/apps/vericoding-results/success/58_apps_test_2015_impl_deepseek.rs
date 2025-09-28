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

proof fn lemma_max_properties(r: int, g: int, b: int)
    requires valid_input(r, g, b)
    ensures
        max_of_3(r, g, b) >= r,
        max_of_3(r, g, b) >= g,
        max_of_3(r, g, b) >= b,
        r + g + b >= max_of_3(r, g, b) + 2
{
    reveal(max_of_3);
}

proof fn lemma_arrangement_condition(r: int, g: int, b: int)
    requires valid_input(r, g, b)
    ensures can_arrange(r, g, b) == (2 * max_of_3(r, g, b) <= r + g + b + 1)
{
    reveal(can_arrange);
}

// </vc-helpers>

// <vc-spec>
fn check_lamp_arrangement(r: i8, g: i8, b: i8) -> (result: bool)
    requires valid_input(r as int, g as int, b as int)
    ensures result == can_arrange(r as int, g as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed compilation errors by avoiding direct use of int/nat in exec code */
    let max_count_i8 = if r >= g && r >= b {
        r
    } else if g >= r && g >= b {
        g
    } else {
        b
    };
    
    let total = (r as i32) + (g as i32) + (b as i32);
    let max_count = max_count_i8 as i32;
    
    (2 * max_count) <= total + 1
}
// </vc-code>


}

fn main() {}