// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn eq_i32(a: i32, b: i32) -> bool { a == b }
// </vc-helpers>

// <vc-spec>
fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
// </vc-spec>
// <vc-code>
{
    let result: bool = if a == b { true } else { false };
    result
}
// </vc-code>

}
fn main() {}