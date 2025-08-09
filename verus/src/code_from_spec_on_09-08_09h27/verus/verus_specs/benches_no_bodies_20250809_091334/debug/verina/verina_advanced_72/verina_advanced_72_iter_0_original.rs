use vstd::prelude::*;

verus! {

// Precondition function
spec fn single_digit_prime_factor_precond(n: nat) -> bool {
    true
}

// Main function
fn single_digit_prime_factor(n: u32) -> (result: u32)
    requires single_digit_prime_factor_precond(n as nat),
    ensures single_digit_prime_factor_postcond(n as nat, result as nat),
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Postcondition function
spec fn single_digit_prime_factor_postcond(n: nat, result: nat) -> bool {
    // result ∈ [0, 2, 3, 5, 7]
    (result == 0 || result == 2 || result == 3 || result == 5 || result == 7) &&
    // (result = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0)))
    (result == 0 ==> (n == 0 || (n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0))) &&
    // (result ≠ 0 → n ≠ 0 ∧ n % result == 0 ∧ (List.range result).all (fun x => x ∈ [2, 3, 5, 7] → n % x ≠ 0))
    (result != 0 ==> (n != 0 && n % result == 0 && smaller_prime_factors_dont_divide(n, result)))
}

// Helper function to check that smaller prime factors don't divide n
spec fn smaller_prime_factors_dont_divide(n: nat, result: nat) -> bool {
    if result == 2 {
        true // no smaller prime factors to check
    } else if result == 3 {
        n % 2 != 0
    } else if result == 5 {
        n % 2 != 0 && n % 3 != 0
    } else if result == 7 {
        n % 2 != 0 && n % 3 != 0 && n % 5 != 0
    } else {
        true
    }
}

} // verus!

fn main() {}