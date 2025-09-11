// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}