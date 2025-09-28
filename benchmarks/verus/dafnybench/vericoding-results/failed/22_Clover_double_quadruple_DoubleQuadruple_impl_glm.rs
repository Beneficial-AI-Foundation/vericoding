use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
  (2 * x, 4 * x)
}
// </vc-code>

fn main() {}

}