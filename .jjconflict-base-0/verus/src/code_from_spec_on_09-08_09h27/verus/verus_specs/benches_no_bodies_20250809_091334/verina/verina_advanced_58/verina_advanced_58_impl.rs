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
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while num % 2 == 0
        invariant num > 0
        decreases num
    {
        num = num / 2;
    }
    
    // Remove all factors of 3
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while num % 3 == 0
        invariant num > 0
        decreases num
    {
        num = num / 3;
    }
    
    // Remove all factors of 5
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while num % 5 == 0
        invariant num > 0
        decreases num
    {
        num = num / 5;
    }
    
    // If num is 1, then original number was ugly
    num == 1
}

// Main function to find nth ugly number
fn nth_ugly_number(n: u32) -> (result: u32)
    requires nth_ugly_number_precond(n as nat) && n <= 20,
    ensures result > 0
{
    let mut ugly_numbers: Vec<u32> = Vec::new();
    ugly_numbers.push(1); // First ugly number is 1
    
    let mut i2 = 0usize;
    let mut i3 = 0usize;
    let mut i5 = 0usize;
    
    let mut next_multiple_of_2 = 2u32;
    let mut next_multiple_of_3 = 3u32;
    let mut next_multiple_of_5 = 5u32;
    
    /* code modified by LLM (iteration 1): added loop invariants and decreases clause */
    while ugly_numbers.len() < n as usize
        invariant ugly_numbers.len() > 0,
            ugly_numbers@[0] == 1,
            i2 < ugly_numbers.len(),
            i3 < ugly_numbers.len(),
            i5 < ugly_numbers.len(),
            next_multiple_of_2 > 0,
            next_multiple_of_3 > 0,
            next_multiple_of_5 > 0
        decreases n as usize - ugly_numbers.len()
    {
        let next_ugly = if next_multiple_of_2 <= next_multiple_of_3 && next_multiple_of_2 <= next_multiple_of_5 {
            next_multiple_of_2
        } else if next_multiple_of_3 <= next_multiple_of_5 {
            next_multiple_of_3
        } else {
            next_multiple_of_5
        };
        
        ugly_numbers.push(next_ugly);
        
        if next_ugly == next_multiple_of_2 {
            i2 = i2 + 1;
            if i2 < ugly_numbers.len() {
                next_multiple_of_2 = ugly_numbers[i2] * 2;
            }
        }
        if next_ugly == next_multiple_of_3 {
            i3 = i3 + 1;
            if i3 < ugly_numbers.len() {
                next_multiple_of_3 = ugly_numbers[i3] * 3;
            }
        }
        if next_ugly == next_multiple_of_5 {
            i5 = i5 + 1;
            if i5 < ugly_numbers.len() {
                next_multiple_of_5 = ugly_numbers[i5] * 5;
            }
        }
    }
    
    ugly_numbers[n as usize - 1]
}

// Postcondition specification  
spec fn nth_ugly_number_postcond(n: nat, result: nat) -> bool {
    result > 0
}

fn main() {
    /* code modified by LLM (iteration 1): removed println! calls as they are not supported in Verus */
    let first_ugly = nth_ugly_number(1);
    // First ugly number computed
    
    let tenth_ugly = nth_ugly_number(10);
    // Tenth ugly number computed
}

}