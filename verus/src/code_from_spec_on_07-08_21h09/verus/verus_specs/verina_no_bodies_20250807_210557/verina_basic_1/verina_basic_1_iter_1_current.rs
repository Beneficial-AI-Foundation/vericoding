use vstd::prelude::*;

verus! {

// Precondition - in Lean this was just True, so no constraints
spec fn has_opposite_sign_precond(a: int, b: int) -> bool {
    true
}

// Main function as a spec function since it works with mathematical integers
spec fn has_opposite_sign(a: int, b: int) -> bool
    recommends has_opposite_sign_precond(a, b)
{
    a * b < 0
}

// Postcondition specification matching the original Lean code
spec fn has_opposite_sign_postcond(a: int, b: int, result: bool) -> bool
    recommends has_opposite_sign_precond(a, b)
{
    (((a < 0 && b > 0) || (a > 0 && b < 0)) ==> result) &&
    (!((a < 0 && b > 0) || (a > 0 && b < 0)) ==> !result)
}

// Proof that the function satisfies its postcondition
proof fn has_opposite_sign_spec_satisfied(a: int, b: int)
    requires has_opposite_sign_precond(a, b)
    ensures has_opposite_sign_postcond(a, b, has_opposite_sign(a, b))
{
    let result = has_opposite_sign(a, b);
    
    // We need to prove both directions of the equivalence:
    // 1. If (a < 0 && b > 0) || (a > 0 && b < 0), then a * b < 0
    // 2. If !((a < 0 && b > 0) || (a > 0 && b < 0)), then !(a * b < 0)
    
    if (a < 0 && b > 0) || (a > 0 && b < 0) {
        // Case 1: opposite signs
        if a < 0 && b > 0 {
            // a is negative, b is positive, so a * b is negative
            assert(a * b < 0);
        } else if a > 0 && b < 0 {
            // a is positive, b is negative, so a * b is negative
            assert(a * b < 0);
        }
        assert(result);
    } else {
        // Case 2: not opposite signs
        // This means: (a >= 0 || b <= 0) && (a <= 0 || b >= 0)
        // Which simplifies to: (a == 0) || (b == 0) || (a > 0 && b > 0) || (a < 0 && b < 0)
        if a == 0 || b == 0 {
            // If either is zero, product is zero, so not negative
            assert(a * b >= 0);
        } else if a > 0 && b > 0 {
            // Both positive, product is positive
            assert(a * b > 0);
        } else if a < 0 && b < 0 {
            // Both negative, product is positive
            assert(a * b > 0);
        }
        assert(a * b >= 0);
        assert(!result);
    }
}

} // verus!

fn main() {}