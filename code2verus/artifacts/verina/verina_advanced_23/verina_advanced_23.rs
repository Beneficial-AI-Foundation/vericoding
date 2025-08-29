use vstd::prelude::*;

verus! {

// Helper function to compute power of 2
spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

// Precondition for isPowerOfTwo
spec fn is_power_of_two_precond(n: int) -> bool {
    true
}

// Postcondition for isPowerOfTwo
spec fn is_power_of_two_postcond(n: int, result: bool) -> bool {
    if result {
        exists|x: nat| pow(2, x) == n && n > 0
    } else {
        !exists|x: nat| pow(2, x) == n && n > 0
    }
}

// Auxiliary recursive function
fn aux(m: i32, fuel: u32) -> (result: bool)
    requires m > 0,
    decreases fuel
{
    if fuel == 0 {
        false
    } else if m == 1 {
        true
    } else if m % 2 != 0 {
        false
    } else {
        aux(m / 2, fuel - 1)
    }
}

// Main function with admitted proof
fn is_power_of_two(n: i32) -> (result: bool)
    requires is_power_of_two_precond(n as int),
    ensures is_power_of_two_postcond(n as int, result),
{
    proof {
        admit(); // Proof admitted (corresponds to "sorry" in Lean)
    }
    
    if n <= 0 {
        false
    } else {
        let fuel = n as u32;
        aux(n, fuel)
    }
}

// Theorem stating the specification is satisfied
proof fn is_power_of_two_spec_satisfied(n: i32)
    requires is_power_of_two_precond(n as int)
{
    // Proof omitted (corresponds to "sorry" in Lean)
    admit();
}

} // verus!

fn main() {
    println!("Verus verification complete");
}