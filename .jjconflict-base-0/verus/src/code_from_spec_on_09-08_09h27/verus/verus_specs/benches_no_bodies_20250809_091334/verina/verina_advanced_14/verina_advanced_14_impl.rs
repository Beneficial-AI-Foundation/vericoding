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
    if n == 1 {
        true
    } else if n == 0 || n % 4 != 0 {
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
    if n == 1 {
        true
    } else if n == 0 || n % 4 != 0 {
        false
    } else {
        let mut current = n;
        /* code modified by LLM (iteration 1): added decreases clause to while loop */
        while current > 1 && current % 4 == 0
            invariant 
                current > 0,
                (exists|m: nat| (n as nat) == pow(4, m)) <==> (exists|k: nat| (current as nat) == pow(4, k))
            decreases current
        {
            current = current / 4;
        }
        current == 1
    }
}

}

fn main() {
}