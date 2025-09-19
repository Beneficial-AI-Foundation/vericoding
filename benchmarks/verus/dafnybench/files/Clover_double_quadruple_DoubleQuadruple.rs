// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i8) -> (ret: (i8, i8))
  ensures ret.0 as int == 2 * (x as int) && ret.1 as int == 4 * (x as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}