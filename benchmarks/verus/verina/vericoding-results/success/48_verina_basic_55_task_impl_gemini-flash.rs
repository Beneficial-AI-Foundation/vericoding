// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed duplicate function definition. The `compare` function is part of the `vc-spec` section, so it does not need to be redefined as a helper. */

// </vc-helpers>

// <vc-spec>
fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implementation of compare function body. */
{
    a == b
}
// </vc-code>

}
fn main() {}