// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn compare_spec(a: i32, b: i32) -> (result: bool) ensures (a == b ==> result == true) && (a != b ==> result == false) { a == b }
// </vc-helpers>

// <vc-spec>
fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
// </vc-spec>
// <vc-code>
{
    let result = a == b;
    result
}
// </vc-code>

}
fn main() {}