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
    
    // Find the largest quotient q such that q <= n/2 and n - d*q < d
    while q <= max_q
        invariant
            0 <= q <= max_q + 1,
            max_q == n / 2,
    {
        let potential_r = n - d * q;
        if potential_r < d {
            // Found a valid solution
            assert(d * q + potential_r == n);
            assert(0 <= q && q <= n / 2);
            assert(0 <= potential_r && potential_r < d);
            return (q, potential_r);
        }
        q = q + 1;
    }
    
    // If we reach here, no solution exists within the constraints
    // This happens when the specification is unsatisfiable
    // We'll return the best attempt (this will fail verification if truly unsatisfiable)
    let final_q = n / 2;
    let final_r = n - d * final_q;
    
    proof {
        // Help the prover understand the arithmetic
        assert(d * final_q + final_r == n);
    }
    
    (final_q, final_r)
}

}