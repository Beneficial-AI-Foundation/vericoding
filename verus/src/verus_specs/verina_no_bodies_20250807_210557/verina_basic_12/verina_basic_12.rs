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
    // The proof follows from the definition of cube_surface_area
    // Since cube_surface_area(size) = 6 * size * size,
    // both result - 6 * size * size = 0 and 6 * size * size - result = 0 hold
}

}

fn main() {}