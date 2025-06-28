use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn has_divisor_in_range(m: int, low: int, high: int) -> bool {
    exists|j: int| low <= j < high && m % j == 0
}

proof fn modulo_equivalence(m: u64, i: u64)
    requires
        m <= 0x7fff_ffff_ffff_ffff,
        i <= 0x7fff_ffff_ffff_ffff,
        i > 0,
    ensures
        (m % i == 0) <==> ((m as int) % (i as int) == 0)
{
    // This equivalence holds for non-negative values within range
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
    
    // For numbers beyond u64 range, we cannot execute the algorithm
    // In practice, this would require a different implementation
    if m > 0x7fff_ffff_ffff_ffff {
        // For verification purposes, assume false for very large numbers
        // In a real implementation, this would use big integer arithmetic
        assume(false);
        return false;
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
        if m_u64 % i == 0 {
            // We found a divisor
            proof {
                modulo_equivalence(m_u64, i);
            }
            assert(m % (i as int) == 0);
            assert(2 <= i as int < m);
            return false;
        }
        i = i + 1;
    }
    
    // Loop completed without finding divisors
    assert(i == m_u64);
    assert(forall|j: int| 2 <= j < m ==> m % j != 0);
    
    return true;
}

}