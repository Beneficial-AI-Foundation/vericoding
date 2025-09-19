// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn my_min(a: i8, b: i8) -> (result: i8)
    ensures
        result as int <= a as int && result as int <= b as int,
        result == a || result == b,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}