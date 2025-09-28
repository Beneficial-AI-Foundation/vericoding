// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, p: int) -> bool {
    0 <= a <= 100 && 0 <= p <= 100
}

spec fn total_pieces(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    a * 3 + p
}

spec fn max_pies(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    total_pieces(a, p) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn calculate_max_pies(a: i8, p: i8) -> (pies: i8)
    requires 
        valid_input(a as int, p as int)
    ensures 
        pies as int == max_pies(a as int, p as int) &&
        pies >= 0 &&
        pies as int == (a as int * 3 + p as int) / 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): ensure result is within i8 range and nonnegative */
    let total = (a as i32) * 3 + (p as i32);
    let pies_val = total / 2;
    let pies = if pies_val > 127 {
        127
    } else if pies_val < 0 {
        0
    } else {
        pies_val as i8
    };
    pies
}
// </vc-code>


}

fn main() {}