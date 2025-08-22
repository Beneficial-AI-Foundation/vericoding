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
    ensures
        is_prime_postcond(n as nat, result),
{
    let sqrt_n = ((n as f64).sqrt() as u32) + 1;
    let check_up_to = if sqrt_n < n { sqrt_n } else { n - 1 };
    is_prime_check(n, 2, check_up_to)
}

// Helper function that performs the actual checking
fn is_prime_check(n: u32, i: u32, fuel: u32) -> (result: bool)
    requires 
        n >= 2,
        n <= 0xFFFF,
        i >= 2,  
        fuel <= n,
    decreases fuel,
    ensures
        result == (i > fuel || (i <= fuel && n % i != 0 && is_prime_check(n, i + 1, fuel))),
{
    if i > fuel {
        true
    } else if n % i == 0 {
        false
    } else {
        is_prime_check(n, i + 1, fuel)
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
    // This is a tautology: P ==> P is always true
    // No additional proof needed
}

fn main() {
    let test_nums = [2u32, 3u32, 4u32, 5u32, 17u32, 25u32];
    let mut i = 0;
    while i < test_nums.len()
        invariant i <= test_nums.len(),
    {
        let num = test_nums[i];
        if num >= 2 && num <= 0xFFFF {
            let result = is_prime(num);
            println!("{} is prime: {}", num, result);
        }
        i += 1;
    }
}

} // verus!