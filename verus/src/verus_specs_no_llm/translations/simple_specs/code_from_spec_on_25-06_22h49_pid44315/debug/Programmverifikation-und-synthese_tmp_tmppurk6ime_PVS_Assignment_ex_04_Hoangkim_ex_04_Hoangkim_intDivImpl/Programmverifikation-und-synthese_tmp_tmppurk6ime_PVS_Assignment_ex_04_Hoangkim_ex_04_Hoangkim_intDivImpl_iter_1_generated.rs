use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn intDivImpl(n: int, d: int) -> (q: int, r: int)
    requires
        n >= d && n >= 0 && d > 0
    ensures
        (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d
{
    let mut quotient = 0;
    let mut remainder = n;
    
    while remainder >= d && quotient < n/2
        invariant
            d * quotient + remainder == n,
            quotient >= 0,
            remainder >= 0,
            quotient <= n/2,
    {
        quotient = quotient + 1;
        remainder = remainder - d;
    }
    
    assert(d * quotient + remainder == n);
    assert(quotient <= n/2);
    assert(remainder >= 0);
    
    // We need to ensure remainder < d
    // If remainder >= d, then we can't increment quotient further due to q <= n/2 constraint
    // In this case, we still have a valid solution where remainder might be >= d
    // But the postcondition requires remainder < d
    
    // Let's reconsider: if we can't make remainder < d while keeping q <= n/2,
    // we need to find a different valid solution
    
    if remainder >= d {
        // We need to satisfy the postcondition, so let's find the maximum q such that
        // q <= n/2 and we can make remainder < d
        let max_q = n / 2;
        if d * max_q <= n {
            let new_remainder = n - d * max_q;
            if new_remainder < d {
                return (max_q, new_remainder);
            }
        }
        
        // If we still can't satisfy remainder < d, try smaller quotients
        let mut test_q = quotient;
        while test_q >= 0 {
            let test_r = n - d * test_q;
            if test_r < d && test_q <= n/2 {
                return (test_q, test_r);
            }
            test_q = test_q - 1;
        }
    }
    
    (quotient, remainder)
}

}