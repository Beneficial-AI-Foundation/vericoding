use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn cal_div() -> (result: (i32, i32))
  ensures result.0 == 191i32 / 7i32 && result.1 == 191i32 % 7i32,
// </vc-spec>
// <vc-code>
{
  let q: i32 = 191i32 / 7i32;
  let r: i32 = 191i32 % 7i32;
  (q, r)
}
// </vc-code>

fn main() {
}

}