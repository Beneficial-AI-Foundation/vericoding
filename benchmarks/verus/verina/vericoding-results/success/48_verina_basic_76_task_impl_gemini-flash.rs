// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: i32, b: i32) -> (result: i32)
    ensures
        (a <= b ==> result == a),
        (a > b ==> result == b),
{
    if a < b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
{
    let result = min(x, y);
    result
}
// </vc-code>

}
fn main() {}