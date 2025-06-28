use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPrime(m: int) -> (isPrime: bool)
    requires
        m > 0 // m must be greater than 0
    ensures
        isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0) 
        // states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
{
    if m <= 1 {
        return false;
    }
    
    let mut i = 2;
    while i < m
        invariant
            2 <= i <= m,
            forall j : int :: 2 <= j < i ==> m % j != 0,
    {
        if m % i == 0 {
            return false;
        }
        i = i + 1;
    }
    
    return true;
}

}

The implementation works as follows:


   - Use a while loop with iterator `i` starting from 2
   - The loop invariant ensures that:
     - `i` stays in bounds (`2 <= i <= m`)
     - All numbers from 2 to `i-1` are not divisors of `m`
   - If we find any divisor (`m % i == 0`), return `false`
   - Otherwise, increment `i` and continue


The loop invariant is crucial for verification - it maintains that all numbers we've already checked (from 2 to `i-1`) are not divisors of `m`. When the loop terminates, we know that no number in the range `[2, m)` divides `m`, which combined with `m > 1` gives us the definition of primality in the postcondition.