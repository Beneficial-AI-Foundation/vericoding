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
  requires x <= i32::MAX / 4 && x >= i32::MIN / 4,
  let doubled = 2 * x;
  let quadrupled = 4 * x;
  (doubled, quadrupled)
}
// </vc-code>

fn main() {}

}