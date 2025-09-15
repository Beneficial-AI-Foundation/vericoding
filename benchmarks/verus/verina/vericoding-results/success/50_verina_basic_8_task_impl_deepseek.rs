// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn my_min_internal(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a <= b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn my_min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
// </vc-spec>
// <vc-code>
{
    let result = my_min_internal(a, b);
    result
}
// </vc-code>

}
fn main() {}