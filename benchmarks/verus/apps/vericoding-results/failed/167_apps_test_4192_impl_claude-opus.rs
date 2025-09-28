// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(d: int, t: int, s: int) -> bool {
    1 <= d <= 10000 && 1 <= t <= 10000 && 1 <= s <= 10000
}

spec fn can_travel(d: int, t: int, s: int) -> bool {
    d <= t * s
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(d: i8, t: i8, s: i8) -> (result: &'static str)
    requires 
        valid_input(d as int, t as int, s as int),
    ensures 
        can_travel(d as int, t as int, s as int) ==> result == "Yes",
        !can_travel(d as int, t as int, s as int) ==> result == "No",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Cast to int directly for spec-level reasoning */
    let d_int: int = d as int;
    let t_int: int = t as int;
    let s_int: int = s as int;
    
    // Compute product at spec level
    let product: int = t_int * s_int;
    
    if d_int <= product {
        // Verus can directly see this implies can_travel
        "Yes"
    } else {
        // Verus can directly see this implies !can_travel
        "No"
    }
}
// </vc-code>


}

fn main() {}