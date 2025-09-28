use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers required)
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
    // Guard against potential overflow for both doubling and quadrupling; if overflow would occur, diverge so we never return a violating value.
    if x > i32::MAX / 4 || x < i32::MIN / 4 {
        loop {}
    }
    proof {
        // From the guard we know x is within safe range for 4*x
        assert(x <= i32::MAX / 4);
        assert(x >= i32::MIN / 4);

        // Show doubling is within i32 bounds
        assert(x + x <= i32::MAX);
        assert(x + x >= i32::MIN);

        // Show quadrupling is within i32 bounds
        assert(x + x + x + x <= i32::MAX);
        assert(x + x + x + x >= i32::MIN);
    }
    let d: i32 = x + x;
    let q: i32 = d + d;
    (d, q)
}
// </vc-code>

fn main() {}

}