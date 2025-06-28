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
        // Adding the (2*i + 1)th odd number
        sum = sum + (2 * i + 1);
        i = i + 1;
        
        // Proof annotation to help Verus understand the mathematical relationship
        // After adding the ith odd number (2*i + 1), we have:
        // new_sum = old_sum + (2*i + 1) = i*i + (2*i + 1) = (i+1)*(i+1)
        assert(sum == i * i);
    }
    
    // When the loop exits, i == n and sum == i * i == n * n
    assert(i == n);
    assert(sum == i * i);
    
    sum
}

}