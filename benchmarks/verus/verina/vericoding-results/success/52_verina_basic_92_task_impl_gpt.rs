// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add postconditions specifying swap semantics */
fn swap_pair(a: i32, b: i32) -> (result: (i32, i32))
    ensures
        result.0 == b,
        result.1 == a,
{
    (b, a)
}
// </vc-helpers>

// <vc-spec>
fn swap_arithmetic(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> (result.0 != x && result.1 != y),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use helper with ensures to satisfy swap postconditions */
    let r = swap_pair(x, y);
    r
}
// </vc-code>

}
fn main() {}