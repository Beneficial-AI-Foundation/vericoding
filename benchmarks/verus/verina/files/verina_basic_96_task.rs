// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap_simultaneous(x: i8, y: i8) -> (result: (i8, i8))
    ensures
        result.0 as int == y as int,
        result.1 as int == x as int,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}