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
            // We found a divisor, so m is not prime
            assert(2 <= i < m && m % i == 0);
            // This contradicts the primality condition
            assert(!(forall j : int :: 2 <= j < m ==> m % j != 0));
            return false;
        }
        i = i + 1;
    }
    
    // Loop terminated with i == m
    assert(i == m);
    // From the invariant, we know no divisors exist in [2, i)
    assert(forall j : int :: 2 <= j < i ==> m % j != 0);
    // Since i == m, this means no divisors exist in [2, m)
    assert(forall j : int :: 2 <= j < m ==> m % j != 0);
    // We already checked m > 1, so m is prime
    assert(m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0);
    return true;
}

}