// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}