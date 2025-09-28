use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
  let d = x + x;
  let q = d + d;
  assert(d == 2 * x);
  assert(q == 4 * x);
  (d, q)
}
// </vc-code>

fn main() {}

}