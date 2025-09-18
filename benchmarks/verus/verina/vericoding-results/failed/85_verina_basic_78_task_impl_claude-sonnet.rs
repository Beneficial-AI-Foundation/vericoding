// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow safety preconditions */
fn add_safe(x: i32, y: i32) -> (result: i32)
    requires
        x as int + y as int >= i32::MIN as int,
        x as int + y as int <= i32::MAX as int,
    ensures
        result as int == x as int + y as int,
{
    x + y
}

fn sub_safe(x: i32, y: i32) -> (result: i32)
    requires
        x as int - y as int >= i32::MIN as int,
        x as int - y as int <= i32::MAX as int,
    ensures
        result as int == x as int - y as int,
{
    x - y
}
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using safe arithmetic operations */
    let sum = add_safe(x, y);
    let diff = sub_safe(x, y);
    let result = (sum, diff);
    result
}
// </vc-code>

}
fn main() {}