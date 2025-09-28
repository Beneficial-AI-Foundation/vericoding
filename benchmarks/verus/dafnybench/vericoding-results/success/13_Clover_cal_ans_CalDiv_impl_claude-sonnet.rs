use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cal_div() -> (result: (i32, i32))
  ensures result.0 == 191i32 / 7i32 && result.1 == 191i32 % 7i32,
// </vc-spec>
// <vc-code>
{
  let quotient = 191i32 / 7i32;
  let remainder = 191i32 % 7i32;
  (quotient, remainder)
}
// </vc-code>

fn main() {
}

}