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
        proof {
            assert(old_sum == Sum(old_i)); // From loop invariant
            assert(i == old_i + 1);
            assert(sum == old_sum + i);
            assert(sum == old_sum + (old_i + 1));
            assert(sum == Sum(old_i) + (old_i + 1));
            
            // By definition of Sum, Sum(i) = Sum(old_i + 1) = (old_i + 1) + Sum(old_i)
            assert(i > 0);
            assert(Sum(i) == i + Sum((i - 1) as nat));
            assert(i - 1 == old_i);
            assert(Sum(i) == (old_i + 1) + Sum(old_i));
            assert(Sum(i) == Sum(old_i) + (old_i + 1));
            assert(sum == Sum(i));
        }
    }
    
    sum
}

}