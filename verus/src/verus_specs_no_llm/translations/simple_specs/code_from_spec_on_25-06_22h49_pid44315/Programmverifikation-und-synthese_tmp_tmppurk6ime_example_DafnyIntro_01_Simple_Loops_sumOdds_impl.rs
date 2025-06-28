use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sumOdds(n: nat) -> (sum: nat)
    ensures
        sum == n * n
{
    let mut sum: nat = 0;
    let mut i: nat = 0;
    
    while i < n
        invariant
            sum == i * i,
            i <= n,
    {
        // Store old values for proof
        let old_sum = sum;
        let old_i = i;
        
        // Adding the (2*i + 1)th odd number
        sum = sum + (2 * i + 1);
        i = i + 1;
        
        // Proof that the invariant is maintained
        assert(old_sum == old_i * old_i);
        assert(i == old_i + 1);
        assert(sum == old_sum + (2 * old_i + 1));
        assert(sum == old_i * old_i + (2 * old_i + 1));
        
        // Show the algebraic identity: old_i² + 2*old_i + 1 = (old_i + 1)²
        assert(old_i * old_i + 2 * old_i + 1 == (old_i + 1) * (old_i + 1)) by(nonlinear_arith);
        assert(sum == i * i);
    }
    
    sum
}

}