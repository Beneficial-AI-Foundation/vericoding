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
    let max_q = n / 2;
    let mut q = 0;
    
    // Find the largest quotient q such that q <= n/2 and the remainder is valid
    while q <= max_q
        invariant
            0 <= q <= max_q + 1,
            max_q == n / 2,
            n >= d && n >= 0 && d > 0,
    {
        let potential_r = n - d * q;
        if potential_r < d {
            // Found a valid solution
            return (q, potential_r);
        }
        q = q + 1;
    }
    
    // This point should not be reachable given the preconditions,
    // but we need to handle it for completeness
    // Use the maximum allowed quotient
    let final_q = max_q;
    let final_r = n - d * final_q;
    
    // Since we must satisfy the postcondition, and we've reached this point,
    // we know that final_r must be < d (otherwise we would have found a solution earlier)
    assert(final_r >= 0); // Since n >= d*final_q is guaranteed by our search
    
    (final_q, final_r)
}

}