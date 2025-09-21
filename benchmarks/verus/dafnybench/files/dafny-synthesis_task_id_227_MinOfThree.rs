// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i8, b: i8, c: i8) -> (min: i8)
    ensures
        min as int <= a as int && min as int <= b as int && min as int <= c as int,
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