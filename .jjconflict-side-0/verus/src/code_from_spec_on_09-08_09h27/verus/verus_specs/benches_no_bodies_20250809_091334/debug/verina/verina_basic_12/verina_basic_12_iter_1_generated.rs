- The postcondition requires: `(result - 6 * size * size == 0) && (6 * size * size - result == 0)`
- The result is `cube_surface_area(size)` which returns `6 * size * size`
- So I need to prove: `(6 * size * size - 6 * size * size == 0) && (6 * size * size - 6 * size * size == 0)`

This is trivially true since both expressions equal 0.

use vstd::prelude::*;

verus! {

// Precondition function
spec fn cube_surface_area_precond(size: nat) -> bool {
    true
}

// Main function - using nat for simplicity to match Lean
spec fn cube_surface_area(size: nat) -> nat {
    6 * size * size
}

// Postcondition function (equivalent to the Lean postcondition)
spec fn cube_surface_area_postcond(size: nat, result: nat) -> bool {
    (result - 6 * size * size == 0) && (6 * size * size - result == 0)
}

// Proof that the specification is satisfied
proof fn cube_surface_area_spec_satisfied(size: nat)
    requires cube_surface_area_precond(size)
    ensures cube_surface_area_postcond(size, cube_surface_area(size))
{
    // The proof is trivial since cube_surface_area(size) = 6 * size * size
    // So we need to prove:
    // (6 * size * size - 6 * size * size == 0) && (6 * size * size - 6 * size * size == 0)
    // Both expressions are 0, so this is automatically verified
}

}

fn main() {}