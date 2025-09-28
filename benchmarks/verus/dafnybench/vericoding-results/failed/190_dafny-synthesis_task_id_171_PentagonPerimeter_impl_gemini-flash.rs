use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
spec fn mul_spec(a: i32, b: i32) -> i32 {
    a * b
}

proof fn mul_by_5_distributes_over_pos(side: i32)
    requires
        side > 0
    ensures
        5 * side == mul_spec(5, side)
{
    // This proof block is just to satisfy the `ensures` clause using `mul_spec`.
    // In Verus, basic arithmetic operations like multiplication are `spec` by default
    // and do not need explicit proof like this for simple `==` assertions unless
    // a more complex property is being derived or a `via_fn` is used.
    // The previous error was due to `#[via_fn(mul_spec)]` not having a function body.
}
// </vc-helpers>

// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// <vc-code>
{
    let perimeter: i32 = 5 * side;
    proof {
        mul_by_5_distributes_over_pos(side); // Call the helper proof function
        assert(5 * side == mul_spec(5, side)); // This assertion is directly true based on the definition of mul_spec
        assert(perimeter == mul_spec(5, side)); // This assertion is true by transitivity, perimeter == 5 * side
    }
    perimeter
}
// </vc-code>

fn main() {
}

}