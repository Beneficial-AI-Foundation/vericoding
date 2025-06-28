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
        let old_i = i;
        let old_sum = sum;
        
        i = i + 1;
        sum = sum + i;
        
        // Proof that sum == Sum(i) after the updates
        assert(sum == Sum(i)) by {
            // Before updates: old_sum == Sum(old_i) (from invariant)
            // After updates: i == old_i + 1 and sum == old_sum + i
            // So: sum == Sum(old_i) + (old_i + 1)
            
            // We need to show: Sum(old_i) + (old_i + 1) == Sum(old_i + 1)
            // By definition: Sum(old_i + 1) = (old_i + 1) + Sum(old_i)
            // Which equals: Sum(old_i) + (old_i + 1)
            
            assert(old_i + 1 == i);
            assert(old_sum == Sum(old_i));
            assert(sum == old_sum + i);
            assert(sum == Sum(old_i) + (old_i + 1));
            
            // By definition of Sum(i) where i = old_i + 1:
            // Sum(i) = i + Sum(i-1) = (old_i + 1) + Sum(old_i) = Sum(old_i) + (old_i + 1)
            assert(i > 0);
            assert(Sum(i) == i + Sum((i - 1) as nat));
            assert((i - 1) as nat == old_i);
            assert(Sum(i) == i + Sum(old_i));
            assert(Sum(i) == (old_i + 1) + Sum(old_i));
            assert(Sum(i) == Sum(old_i) + (old_i + 1));
        }
    }
    
    sum
}

}