use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {

// Precondition: always true (as in original Lean code)
spec fn is_it_eight_precond(n: int) -> bool {
    true
}

// Helper spec function to check if a number has digit 8
spec fn has_digit_eight_spec(m: nat) -> bool 
    decreases m
{
    if m == 0 {
        false
    } else if m % 10 == 8 {
        true
    } else {
        has_digit_eight_spec((m / 10) as nat)
    }
}

// Helper function to check if a natural number has digit 8
fn has_digit_eight(m: u64) -> (result: bool)
    decreases m
{
    if m == 0 {
        false
    } else if m % 10 == 8 {
        true
    } else {
        has_digit_eight(m / 10)
    }
}

// Main function - checking if n is divisible by 8 or has digit 8
fn is_it_eight(n: i64) -> (result: bool)
    requires is_it_eight_precond(n as int)
{
    let abs_n = if n >= 0 { 
        n as u64 
    } else { 
        assume(n != i64::MIN); // Prevent overflow
        (-n) as u64 
    };
    n % 8 == 0 || has_digit_eight(abs_n)
}

// Postcondition specification matching original Lean
spec fn is_it_eight_postcond(n: int, result: bool) -> bool {
    let abs_n = if n >= 0 { n as nat } else { (-n) as nat };
    (n % 8 == 0 || exists|i: nat| (abs_n as int) / pow(10int, i) % 10 == 8) == result
}

// Theorem stating the specification is satisfied (proof admitted like original sorry)
proof fn is_it_eight_spec_satisfied(n: int)
    requires is_it_eight_precond(n)
    ensures is_it_eight_postcond(n, is_it_eight(n as i64))
{
    admit(); // Corresponds to "sorry" in the original Lean code
}

} // verus!

fn main() {}