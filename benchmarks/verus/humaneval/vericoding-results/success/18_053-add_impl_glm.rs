// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)

    ensures
        res.is_some() ==> res.unwrap() == x + y,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use checked_add to prevent overflow */
    x.checked_add(y)
}
// </vc-code>

}
fn main() {}