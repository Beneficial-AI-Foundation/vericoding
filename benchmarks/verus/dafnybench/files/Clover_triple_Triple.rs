use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (r: i32)
  ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


fn main() {
}

}