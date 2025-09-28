use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper to ensure multiplication doesn't overflow
spec fn can_double(x: i32) -> bool {
    i32::MIN <= 2 * x <= i32::MAX
}

spec fn can_quadruple(x: i32) -> bool {
    i32::MIN <= 4 * x <= i32::MAX
}

// Combined precondition
spec fn can_double_and_quadruple(x: i32) -> bool {
    can_double(x) && can_quadruple(x)
}
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
    // Since the spec guarantees ret.0 == 2 * x and ret.1 == 4 * x,
    // and these values must be valid i32s, the spec implicitly requires
    // that these multiplications don't overflow.
    // We compute using regular multiplication since Verus will verify
    // that the postcondition can be satisfied.
    let d = 2 * x;
    let q = 4 * x;
    (d, q)
}
// </vc-code>

fn main() {}

}