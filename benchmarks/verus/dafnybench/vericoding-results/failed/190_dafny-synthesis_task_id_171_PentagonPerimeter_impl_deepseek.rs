use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn pentagon_perimeter_lemma(side: int)
    requires side > 0
    ensures 5 * side == 5 * side
{
}

proof fn multiplication_safe(side: int)
    requires 
        0 < side <= (i32::MAX as int) / 5,
    ensures 
        (5 * side) as i32 == 5 * (side as i32)
{
    assert(5 * side <= i32::MAX as int) by {
        assert(side <= (i32::MAX as int) / 5);
    };
}
// </vc-helpers>

// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// <vc-code>
{
    proof {
        pentagon_perimeter_lemma(side as int);
        multiplication_safe(side as int);
    }
    let perimeter = 5 * side;
    assert(perimeter == 5 * side) by (nonlinear_arith);
    perimeter
}
// </vc-code>

fn main() {
}

}