// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x: int, y: int) -> bool
{
    true
}

spec fn correct_sum(x: int, y: int) -> int
{
    x + y
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax error */
fn lemma_add_no_overflow(x: i8, y: i8)
    requires
        x as int + y as int >= -128,
        x as int + y as int <= 127,
    ensures
        (x + y) as int == x as int + y as int
{
    // This lemma establishes that if the sum is within i8 bounds,
    // then the wrapping addition equals the mathematical addition
}

/* helper modified by LLM (iteration 5): added overflow check function */
fn can_add_without_overflow(x: i8, y: i8) -> (result: bool)
    ensures result == (x as int + y as int >= -128 && x as int + y as int <= 127)
{
    let sum = x as i64 + y as i64;
    sum >= -128 && sum <= 127
}
// </vc-helpers>

// <vc-spec>
fn add(x: i8, y: i8) -> (result: i8)
    requires valid_input(x as int, y as int)
    ensures result as int == correct_sum(x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced assertions with conditional overflow handling */
    if can_add_without_overflow(x, y) {
        lemma_add_no_overflow(x, y);
        x + y
    } else {
        // Handle overflow case - clamp to bounds
        let sum = x as int + y as int;
        if sum > 127 {
            127
        } else {
            -128
        }
    }
}
// </vc-code>


}

fn main() {}