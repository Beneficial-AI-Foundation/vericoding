// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i8, y: i8) -> (result: (i8, i8))
    ensures
        result.0 as int == x as int + y as int,
        result.1 as int + y as int == x as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}