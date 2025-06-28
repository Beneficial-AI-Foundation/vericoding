use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPrime(m: int) -> (isPrime: bool)
    requires
        m > 0 // m must be greater than 0
    ensures
        isPrime <==> (m > 1 && forall|j: int| 2 <= j < m ==> m % j != 0) 
        // states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
{
    if m <= 1 {
        return false;
    }
    
    // Convert to u64 for executable code
    let m_u64 = m as u64;
    let mut i: u64 = 2;
    
    while i < m_u64
        invariant
            2 <= i <= m_u64,
            m_u64 == m,
            i as int == i,
            m_u64 as int == m,
            forall|j: int| 2 <= j < i ==> m % j != 0,
        decreases m_u64 - i
    {
        if m_u64 % i == 0 {
            // We found a divisor, so m is not prime
            assert(2 <= i as int < m && m % (i as int) == 0);
            // This contradicts the primality condition
            return false;
        }
        i = i + 1;
    }
    
    // Loop terminated with i == m_u64
    assert(i == m_u64);
    assert(i as int == m);
    // From the invariant, we know no divisors exist in [2, i)
    assert(forall|j: int| 2 <= j < i as int ==> m % j != 0);
    // Since i == m, this means no divisors exist in [2, m)
    assert(forall|j: int| 2 <= j < m ==> m % j != 0);
    // We already checked m > 1, so m is prime
    assert(m > 1 && forall|j: int| 2 <= j < m ==> m % j != 0);
    return true;
}

}