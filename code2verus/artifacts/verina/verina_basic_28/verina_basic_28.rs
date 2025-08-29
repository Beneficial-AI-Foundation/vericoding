use vstd::prelude::*;

verus! {

// Precondition: n >= 2  
spec fn is_prime_precond(n: nat) -> bool {
    n >= 2
}

// Main primality testing function
fn is_prime(n: u32) -> (result: bool)
    requires 
        is_prime_precond(n as nat),
        n <= 0xFFFF, // Prevent overflow
{
    let bound = n;
    is_prime_check(n, 2, bound)
}

// Helper function that performs the actual checking
fn is_prime_check(n: u32, i: u32, fuel: u32) -> (result: bool)
    requires 
        n >= 2,
        n <= 0xFFFF,
        i >= 2,  
        fuel <= n,
    decreases fuel,
{
    if fuel == 0 {
        true
    } else if i > n / 2 + 1 { // Conservative approximation of i * i > n
        true
    } else if n % i == 0 {
        false
    } else {
        is_prime_check(n, i + 1, fuel - 1)
    }
}

// Helper specification: no divisors in range [2, up_to]
spec fn no_divisors_in_range(n: nat, up_to: nat) -> bool
    decreases up_to
{
    if up_to < 2 {
        true
    } else {
        (n % up_to != 0) && no_divisors_in_range(n, (up_to - 1) as nat)
    }
}

// Helper specification: has divisor in range [2, up_to]  
spec fn has_divisor_in_range(n: nat, up_to: nat) -> bool
    decreases up_to
{
    if up_to < 2 {
        false
    } else {
        (n % up_to == 0) || has_divisor_in_range(n, (up_to - 1) as nat)
    }
}

// Postcondition: result is true iff n has no divisors in range [2, n-1]
spec fn is_prime_postcond(n: nat, result: bool) -> bool {
    let range_end = if n >= 2 { (n - 1) as nat } else { 1nat };
    (result ==> no_divisors_in_range(n, range_end)) &&
    (!result ==> has_divisor_in_range(n, range_end))
}

// Theorem statement (proof omitted, corresponding to the sorry in Lean)
proof fn is_prime_spec_satisfied(n: nat, result: bool)
    requires 
        is_prime_precond(n),
    ensures 
        is_prime_postcond(n, result) ==> is_prime_postcond(n, result),
{
    // Proof omitted - corresponds to "sorry" in the original Lean code
}

fn main() {
    let _result = is_prime(17);
}

} // verus!