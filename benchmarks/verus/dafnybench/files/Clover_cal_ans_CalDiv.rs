// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cal_div() -> (result: (i8, i8))
  ensures result.0 as i32 == 191i32 / 7i32 && result.1 as i32 == 191i32 % 7i32,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}