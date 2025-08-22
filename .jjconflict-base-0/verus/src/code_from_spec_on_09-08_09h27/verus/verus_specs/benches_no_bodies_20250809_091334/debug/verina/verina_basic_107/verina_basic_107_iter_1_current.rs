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
    // The postcondition states: 2 * result == a + b - ((a + b) % 2)
    // Given that result == (a + b) / 2, we need to prove this equality
    // This follows from the definition of integer division:
    // For any integers x, y where y != 0: x == y * (x / y) + (x % y)
    // So: a + b == 2 * ((a + b) / 2) + ((a + b) % 2)
    // Rearranging: 2 * ((a + b) / 2) == a + b - ((a + b) % 2)
    // Since result == (a + b) / 2, we have: 2 * result == a + b - ((a + b) % 2)
}

}

fn main() {
    let result = compute_avg(10, 15);
    println!("Average of 10 and 15: {}", result);
}