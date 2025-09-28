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
/* helper modified by LLM (iteration 4): trivial identity helper for i8 to avoid casting from spec int */
fn id_i8(a: i8) -> (b: i8)
    ensures
        b == a,
{
    a
}
// </vc-helpers>

// <vc-spec>
fn add(x: i8, y: i8) -> (result: i8)
    requires valid_input(x as int, y as int)
    ensures result as int == correct_sum(x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute sum as i16 and cast to i8 */
    let sum: i16 = (x as i16) + (y as i16);
    sum as i8
}
// </vc-code>


}

fn main() {}