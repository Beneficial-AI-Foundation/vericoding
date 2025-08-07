use vstd::prelude::*;

verus! {

// Precondition function
spec fn double_quadruple_precond(x: int) -> bool {
    true
}

// Main function with specification
fn double_quadruple(x: int) -> (ret: (int, int))
    requires double_quadruple_precond(x)
    ensures ret.0 == 2 * x && ret.1 == 2 * ret.0
{
    let a = x + x;  // 2 * x
    let b = a + a;  // 2 * a
    (a, b)
}

// Postcondition function (for completeness, though not needed with ensures clause)
spec fn double_quadruple_postcond(x: int, result: (int, int)) -> bool {
    result.0 == 2 * x && result.1 == 2 * result.0
}

// Theorem demonstrating the specification is satisfied
proof fn double_quadruple_spec_satisfied(x: int, result: (int, int))
    requires double_quadruple_precond(x) && result.0 == 2 * x && result.1 == 2 * result.0
    ensures double_quadruple_postcond(x, result)
{
    // The proof is automatic given the requires clause matches the postcondition
}

}

fn main() {
    // Empty main function for compilation
}