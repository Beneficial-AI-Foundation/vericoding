// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result <= a && result <= b && result <= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    let min_ab = if a <= b { a } else { b };
    let result = if min_ab <= c { min_ab } else { c };
    result
}
// </vc-code>

}
fn main() {}