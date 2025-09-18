// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): equality boolean helper with named result */
fn eq_bool(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
{
    if a == b {
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call helper eq_bool and return result */
    let res: bool = eq_bool(a, b);
    res
}
// </vc-code>

}
fn main() {}