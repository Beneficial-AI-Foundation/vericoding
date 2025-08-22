use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {

// Precondition function - corresponds to ifPowerOfFour_precond in Lean
pub open spec fn if_power_of_four_precond(n: nat) -> bool {
    true
}

// Postcondition function - corresponds to ifPowerOfFour_postcond in Lean  
pub open spec fn if_power_of_four_postcond(n: nat, result: bool) -> bool {
    result <==> exists|m: nat| n == pow(4, m)
}

// Helper function to check if a number is a power of 4
// This corresponds to the nested helper function in the original Lean code
fn helper(n: u32) -> (result: bool)
    decreases n
{
    if n == 0 {
        false
    } else if n == 1 {
        true
    } else if n % 4 != 0 {
        false
    } else {
        helper(n / 4)
    }
}

// Main function - corresponds to ifPowerOfFour in Lean
pub fn if_power_of_four(n: u32) -> (result: bool)
    requires if_power_of_four_precond(n as nat)
    ensures if_power_of_four_postcond(n as nat, result)
{
    helper(n)
}

}

fn main() {
    let test_cases = vec![0u32, 1, 2, 3, 4, 5, 8, 16, 17, 64, 256];
    for n in test_cases {
        let result = if_power_of_four(n);
        println!("is_power_of_four({}) = {}", n, result);
    }
}