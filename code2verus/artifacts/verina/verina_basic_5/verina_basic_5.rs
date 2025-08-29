use vstd::prelude::*;

verus! {

// Precondition for multiply function
spec fn multiply_precond(a: int, b: int) -> bool {
    true
}

// Postcondition for multiply function
spec fn multiply_postcond(a: int, b: int, result: int) -> bool {
    result - a * b == 0 && a * b - result == 0
}

// The multiply function
fn multiply(a: int, b: int) -> (result: int)
    requires multiply_precond(a, b)
    ensures multiply_postcond(a, b, result)
{
    a * b
}

// Proof that the function satisfies its specification
proof fn multiply_spec_satisfied(a: int, b: int)
    requires multiply_precond(a, b)
    ensures multiply_postcond(a, b, a * b)
{
    // The proof follows directly from the definitions
}

} // verus!

fn main() {}