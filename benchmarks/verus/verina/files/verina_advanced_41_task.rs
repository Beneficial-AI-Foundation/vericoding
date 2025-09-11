// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}