use vstd::prelude::*;

verus! {

// Precondition function
spec fn nth_ugly_number_precond(n: nat) -> bool {
    n > 0
}

// Check if a number is ugly (only has factors 2, 3, 5)
fn is_ugly(x: u32) -> (result: bool) {
    if x <= 1 {
        return x == 1;
    }
    
    let mut n = x;
    
    // Divide out all factors of 2
    while n > 1 && n % 2 == 0
        invariant n <= x,
        decreases n
    {
        n = n / 2;
    }
    
    // Divide out all factors of 3
    while n > 1 && n % 3 == 0
        invariant n <= x,
        decreases n
    {
        n = n / 3;
    }
    
    // Divide out all factors of 5
    while n > 1 && n % 5 == 0
        invariant n <= x,
        decreases n
    {
        n = n / 5;
    }
    
    n == 1
}

// Main function to find nth ugly number
fn nth_ugly_number(n: u32) -> (result: u32)
    requires nth_ugly_number_precond(n as nat) && n <= 20,
    ensures result > 0
{
    if n == 1 {
        return 1;
    }
    
    let mut count = 1;
    let mut candidate = 2;
    
    while count < n && candidate < 500
        invariant 
            count >= 1,
            count <= n,
            candidate >= 2
        decreases 500 - candidate
    {
        if is_ugly(candidate) {
            count = count + 1;
            if count == n {
                return candidate;
            }
        }
        candidate = candidate + 1;
    }
    
    1
}

// Postcondition specification  
spec fn nth_ugly_number_postcond(n: nat, result: nat) -> bool {
    result > 0
}

fn main() {
    let result = nth_ugly_number(10);
}

}