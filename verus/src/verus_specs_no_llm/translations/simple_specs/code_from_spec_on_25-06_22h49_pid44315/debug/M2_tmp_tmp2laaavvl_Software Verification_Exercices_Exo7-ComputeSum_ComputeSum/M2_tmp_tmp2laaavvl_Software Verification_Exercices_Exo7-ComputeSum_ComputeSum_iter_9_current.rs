use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + Sum((n - 1) as nat) }
}

fn ComputeSum(n: nat) -> (s: nat)
    ensures
        s == Sum(n)
{
    let mut i: nat = 0;
    let mut sum: nat = 0;
    
    while i < n
        invariant 
            i <= n,
            sum == Sum(i)
        decreases n - i
    {
        i = i + 1;
        sum = sum + i;
        
        // Proof that sum == Sum(i) after the updates
        assert(sum == Sum(i)) by {
            // After the updates: new_i = old_i + 1, new_sum = old_sum + new_i
            // From loop invariant: old_sum == Sum(old_i)
            // So: new_sum = Sum(old_i) + new_i = Sum(old_i) + (old_i + 1)
            // We need: new_sum == Sum(new_i) = Sum(old_i + 1)
            // By definition of Sum: Sum(old_i + 1) = (old_i + 1) + Sum(old_i)
            // This equals our new_sum = Sum(old_i) + (old_i + 1)
            
            assert(i > 0); // Since i was incremented from a value < n
            assert(Sum(i) == i + Sum((i - 1) as nat)); // Definition of Sum for i > 0
        }
    }
    
    sum
}

}