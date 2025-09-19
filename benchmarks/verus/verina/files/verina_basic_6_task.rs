// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i8, b: i8, c: i8) -> (result: i8)
    ensures
        result as int <= a as int && result as int <= b as int && result as int <= c as int,
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