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
        
        // Proof that the invariant is maintained
        // We need to show: old_sum + (2*old_i + 1) == new_i * new_i
        // where old_sum == old_i * old_i and new_i == old_i + 1
        // So: old_i * old_i + (2*old_i + 1) == (old_i + 1) * (old_i + 1)
        // Expanding: old_i * old_i + 2*old_i + 1 == old_i * old_i + 2*old_i + 1 ✓
        assert(sum == (i - 1) * (i - 1) + (2 * (i - 1) + 1));
        assert(sum == (i - 1) * (i - 1) + 2 * (i - 1) + 1);
        assert(sum == i * i) by {
            // The algebraic identity: (i-1)² + 2(i-1) + 1 = i²
            // This follows from (a-1)² + 2(a-1) + 1 = a² - 2a + 1 + 2a - 2 + 1 = a²
        };
    }
    
    sum
}

}