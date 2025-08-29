use vstd::prelude::*;

verus! {

// Precondition for SwapArithmetic
spec fn swap_arithmetic_precond(x: int, y: int) -> bool {
    true
}

// The SwapArithmetic function
fn swap_arithmetic(x: int, y: int) -> (result: (int, int))
    requires swap_arithmetic_precond(x, y)
    ensures result.0 == y && result.1 == x,
            x != y ==> result.0 != x && result.1 != y
{
    let x1 = x;
    let y1 = y;
    let x2 = y1 - x1;
    let y2 = y1 - x2;
    let x3 = y2 + x2;
    (x3, y2)
}

}

fn main() {}