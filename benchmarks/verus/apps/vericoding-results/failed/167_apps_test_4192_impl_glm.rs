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
/* code modified by LLM (iteration 5): use i32 arithmetic to avoid ghost types and prevent overflow */
{
    let d_i32 = d as i32;
    let t_i32 = t as i32;
    let s_i32 = s as i32;
    if d_i32 <= t_i32 * s_i32 {
        "Yes"
    } else {
        "No"
    }
}
// </vc-code>


}

fn main() {}