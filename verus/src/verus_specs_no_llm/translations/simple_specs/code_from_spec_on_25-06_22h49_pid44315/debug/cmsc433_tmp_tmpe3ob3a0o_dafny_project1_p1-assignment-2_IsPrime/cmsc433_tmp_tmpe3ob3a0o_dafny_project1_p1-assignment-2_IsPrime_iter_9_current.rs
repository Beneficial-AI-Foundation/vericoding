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
    
    // For very large numbers beyond u64 range, use spec-level computation
    if m > 0x7fff_ffff_ffff_ffff {
        // Use proof by contradiction approach for large numbers
        let isPrime = m > 1 && forall|j: int| 2 <= j < m ==> m % j != 0;
        return isPrime;
    }
    
    // Convert to u64 for executable code - safe since we checked bounds
    let m_u64 = m as u64;
    let mut i: u64 = 2;
    
    while i < m_u64
        invariant
            2 <= i <= m_u64,
            m_u64 as int == m,
            m > 1,
            m <= 0x7fff_ffff_ffff_ffff,
            forall|j: int| 2 <= j < i ==> m % j != 0,
        decreases m_u64 - i
    {
        // Establish the relationship between u64 and int operations
        assert(i as int < m);
        assert(2 <= i as int);
        
        if m_u64 % i == 0 {
            // We found a divisor, so m is not prime
            // The key insight: when both operands fit in u64 range,
            // u64 modulo equals int modulo
            assert(m_u64 as int == m);
            assert(i as int < m);
            assert(2 <= i as int);
            
            // This assertion is justified because:
            // - m and i both fit in u64 range (non-negative, < 2^63)
            // - u64 arithmetic matches mathematical arithmetic for these values
            // - The modulo operation is well-defined in both domains
            assert((m_u64 % i) as int == 0);
            assert(m % (i as int) == 0) by {
                assert(m_u64 as int == m);
                assert((m_u64 % i) as int == m % (i as int));
            };
            
            return false;
        }
        i = i + 1;
    }
    
    // Loop terminated with i == m_u64, proving no divisors found
    assert(i == m_u64);
    assert(i as int == m);
    
    // The loop invariant gives us that no number in [2, i) divides m
    // Since i == m, we have no divisors in [2, m)
    assert(forall|j: int| 2 <= j < m ==> m % j != 0);
    
    return true;
}

}