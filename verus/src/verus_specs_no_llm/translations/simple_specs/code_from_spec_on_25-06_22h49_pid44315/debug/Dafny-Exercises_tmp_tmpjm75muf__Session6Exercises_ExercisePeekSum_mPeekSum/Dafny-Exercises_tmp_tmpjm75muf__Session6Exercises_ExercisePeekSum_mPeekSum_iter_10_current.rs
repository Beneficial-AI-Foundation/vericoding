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
        v[(n-1) as int] + peekSum(v, (n-1) as nat)
    }
}

// Helper lemma to prove the relationship between peekSum values
proof fn lemma_peekSum_step(v: Vec<int>, n: nat)
    requires
        0 < n <= v.len()
    ensures
        peekSum(v, n) == v[(n-1) as int] + peekSum(v, (n-1) as nat)
{
    // This follows directly from the definition of peekSum
}

// Additional helper lemma for the base case
proof fn lemma_peekSum_zero(v: Vec<int>)
    ensures
        peekSum(v, 0) == 0
{
    // This follows directly from the definition of peekSum
}

// Helper lemma for out of bounds case
proof fn lemma_peekSum_out_of_bounds(v: Vec<int>, n: nat)
    requires
        n > v.len()
    ensures
        peekSum(v, n) == 0
{
    // When n > v.len(), the condition returns 0
}

// Corrected helper lemma for the inductive step in the loop
proof fn lemma_peekSum_increment(v: Vec<int>, i: nat)
    requires
        i < v.len()
    ensures
        peekSum(v, (i+1) as nat) == peekSum(v, i as nat) + v[i as int]
{
    // peekSum(v, i+1) = v[i] + peekSum(v, i) by definition when i+1 > 0 and i+1 <= v.len()
    // This is exactly what we want to prove: peekSum(v, i+1) == peekSum(v, i) + v[i]
    lemma_peekSum_step(v, (i+1) as nat);
}

fn mPeekSum(v: Vec<int>) -> (sum: int)
    requires
        v.len() > 0
    ensures
        sum == peekSum(v, v.len())
{
    let mut sum = 0;
    let mut i: usize = 0;
    
    // Establish initial invariant
    proof {
        lemma_peekSum_zero(v);
    }
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == peekSum(v, i as nat)
    {
        // Prove the step before modifying variables
        proof {
            assert(i < v.len()); // From loop condition
            lemma_peekSum_increment(v, i as nat);
            // This gives us: peekSum(v, (i+1) as nat) == peekSum(v, i as nat) + v[i as int]
        }
        
        sum = sum + v[i];
        i = i + 1;
    }
    
    sum
}

}