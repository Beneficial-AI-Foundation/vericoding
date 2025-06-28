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
            // We know that before the loop iteration:
            // - old_i = i - 1
            // - old_sum = Sum(old_i) = Sum(i - 1)
            // 
            // After the updates:
            // - new_sum = old_sum + i = Sum(i - 1) + i
            //
            // By definition of Sum:
            // Sum(i) = i + Sum(i - 1) = Sum(i - 1) + i
            //
            // Therefore: new_sum = Sum(i - 1) + i = Sum(i)
            
            // This follows directly from the recursive definition of Sum
            // and the fact that we maintained the invariant before this iteration
        }
    }
    
    sum
}

}