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
            // After i = i + 1, we have new_i = old_i + 1
            // After sum = sum + i, we have new_sum = old_sum + new_i
            // From the loop invariant, we know old_sum == Sum(old_i)
            // So new_sum = Sum(old_i) + new_i = Sum(old_i) + (old_i + 1)
            // We need to show this equals Sum(new_i) = Sum(old_i + 1)
            
            // Since new_i = old_i + 1 > 0, by definition:
            // Sum(new_i) = Sum(old_i + 1) = (old_i + 1) + Sum(old_i)
            // This matches our new_sum = Sum(old_i) + (old_i + 1)
            assert(i > 0);
            assert(Sum(i) == i + Sum((i - 1) as nat));
            // The equality follows from the definition of Sum
        }
    }
    
    sum
}

}