use vstd::prelude::*;

verus! {

// Precondition function
spec fn nth_ugly_number_precond(n: nat) -> bool {
    n > 0
}

// Check if a number is ugly (only has factors 2, 3, 5)
fn is_ugly(x: u32) -> (result: bool) {
    if x == 0 {
        return false;
    }
    
    let mut num = x;
    
    // Remove all factors of 2
    while num % 2 == 0
        invariant num > 0
    {
        num = num / 2;
    }
    
    // Remove all factors of 3
    while num % 3 == 0
        invariant num > 0
    {
        num = num / 3;
    }
    
    // Remove all factors of 5
    while num % 5 == 0
        invariant num > 0
    {
        num = num / 5;
    }
    
    // If we're left with 1, it was ugly
    num == 1
}

// Main function to find nth ugly number
fn nth_ugly_number(n: u32) -> (result: u32)
    requires nth_ugly_number_precond(n as nat) && n <= 20,
    ensures result > 0
{
    let mut count = 0u32;
    let mut current = 1u32;
    
    while count < n
        invariant count < n
        invariant current >= 1
    {
        if is_ugly(current) {
            count = count + 1;
            if count == n {
                return current;
            }
        }
        current = current + 1;
    }
    
    current - 1
}

// Postcondition specification  
spec fn nth_ugly_number_postcond(n: nat, result: nat) -> bool {
    result > 0
}

fn main() {
    let result = nth_ugly_number(10);
    println!("10th ugly number is: {}", result);
}

}