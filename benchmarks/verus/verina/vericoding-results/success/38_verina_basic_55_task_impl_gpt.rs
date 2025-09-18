// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_equal_i32(a: i32, b: i32) -> bool { a == b }

proof fn equal_true_iff(a: i32, b: i32)
    ensures
        a == b ==> is_equal_i32(a, b) == true,
        a != b ==> is_equal_i32(a, b) == false
{}

// </vc-helpers>

// <vc-spec>
fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
// </vc-spec>
// <vc-code>
{
    if a == b {
        true
    } else {
        false
    }
}
// </vc-code>

}
fn main() {}