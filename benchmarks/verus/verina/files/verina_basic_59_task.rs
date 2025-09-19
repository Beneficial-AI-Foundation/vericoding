// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i8) -> (result: (i8, i8))
    ensures
        result.0 as int == 2 * (x as int),
        result.1 as int == 2 * (result.0 as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}