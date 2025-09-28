// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): spec helper for equality */
spec fn eq_bool(a: i32, b: i32) -> bool { a == b }
// </vc-helpers>

// <vc-spec>
fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return direct equality */
    a == b
}
// </vc-code>

}
fn main() {}