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
    (a + b) / 2
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
    let sum = (a as int) + (b as int);
    let r = sum / 2;
    
    // We need to prove: 2 * r == sum - (sum % 2)
    // This follows from the division algorithm: sum = 2 * r + (sum % 2)
    // Rearranging: 2 * r = sum - (sum % 2)
    
    // In Verus, we can use the built-in arithmetic properties
    assert(sum == 2 * r + (sum % 2)) by {
        // This is the fundamental division property that Verus should know
    };
    
    // From sum == 2 * r + (sum % 2), we get 2 * r == sum - (sum % 2)
    assert(2 * r == sum - (sum % 2));
    
    // Since result == r, we have our postcondition
    assert(2 * result == sum - (sum % 2));
}

}

fn main() {
}