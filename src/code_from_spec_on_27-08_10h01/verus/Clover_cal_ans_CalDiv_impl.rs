use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn cal_div() -> (result: (i32, i32))
  ensures result.0 == 191i32 / 7i32 && result.1 == 191i32 % 7i32,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  (27i32, 2i32)
}
// </vc-code>

fn main() {
}

}