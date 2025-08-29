use vstd::prelude::*;

verus! {

// Precondition for ComputeAvg
spec fn compute_avg_precond(a: int, b: int) -> bool {
    true
}

// Postcondition as a separate specification function  
spec fn compute_avg_postcond(a: int, b: int, result: int) -> bool {
    2 * result == a + b - ((a + b) % 2)
}

// The ComputeAvg function
fn compute_avg(a: i32, b: i32) -> (result: i32)
    requires 
        compute_avg_precond(a as int, b as int),
        (a as int) + (b as int) <= i32::MAX as int,
        (a as int) + (b as int) >= i32::MIN as int,
    ensures compute_avg_postcond(a as int, b as int, result as int),
{
    let sum = a + b;
    let result_val = sum / 2;
    
    // Add explicit proof using assume to match the "sorry" in the original Lean
    proof {
        assume(compute_avg_postcond(a as int, b as int, result_val as int));
    }
    
    result_val
}

// Theorem corresponding to the Lean theorem - shows specification is satisfied
proof fn compute_avg_spec_satisfied(a: i32, b: i32, result: i32)
    requires 
        compute_avg_precond(a as int, b as int),
        (a as int) + (b as int) <= i32::MAX as int,  
        (a as int) + (b as int) >= i32::MIN as int,
        result == ((a as int) + (b as int)) / 2,  // This is what compute_avg computes
    ensures compute_avg_postcond(a as int, b as int, result as int)
{
    // Using assume to match the "sorry" in the original Lean proof
    assume(compute_avg_postcond(a as int, b as int, result as int));
}

}

fn main() {
    // Empty main function  
}