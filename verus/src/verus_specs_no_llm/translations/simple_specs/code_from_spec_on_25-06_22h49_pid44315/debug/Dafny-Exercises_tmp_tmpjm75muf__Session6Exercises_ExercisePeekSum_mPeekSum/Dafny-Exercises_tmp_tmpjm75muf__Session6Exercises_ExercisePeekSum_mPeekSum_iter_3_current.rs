use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn peekSum(v: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 || n > v.len() {
        0
    } else {
        v[n-1] + peekSum(v, (n-1) as nat)
    }
}

// Helper lemma to prove the relationship between peekSum values
proof fn lemma_peekSum_step(v: Vec<int>, n: nat)
    requires
        0 < n <= v.len()
    ensures
        peekSum(v, n) == v[n-1] + peekSum(v, (n-1) as nat)
{
    // This follows directly from the definition of peekSum
}

fn mPeekSum(v: Vec<int>) -> (sum: int)
    requires
        v.len() > 0
    ensures
        sum == peekSum(v, v.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == peekSum(v, i)
    {
        sum = sum + v[i as int];
        i = i + 1;
        
        // Proof that the invariant is maintained
        proof {
            if i > 0 {
                lemma_peekSum_step(v, i);
                // peekSum(v, i) == v[i-1] + peekSum(v, i-1)
                // We added v[i-1] to sum, so sum == peekSum(v, i)
            }
        }
    }
    
    sum
}

}