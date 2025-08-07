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
        false  // 0 is not a power of 4
    } else if n == 1 {
        true   // 4^0 = 1
    } else if n >= 2 && (n % 4) == 0 {
        helper(n / 4)  // Check if n/4 is a power of 4
    } else {
        false  // Not divisible by 4, so not a power of 4
    }
}

// Main function - corresponds to ifPowerOfFour in Lean
pub fn if_power_of_four(n: u32) -> (result: bool)
    requires if_power_of_four_precond(n as nat)
{
    helper(n)
}

}

fn main() {
    // Test the function
    let result1 = if_power_of_four(1);
    let result4 = if_power_of_four(4);
    let result16 = if_power_of_four(16);
    let result3 = if_power_of_four(3);
    
    println!("1 is power of 4: {}", result1);
    println!("4 is power of 4: {}", result4); 
    println!("16 is power of 4: {}", result16);
    println!("3 is power of 4: {}", result3);
}