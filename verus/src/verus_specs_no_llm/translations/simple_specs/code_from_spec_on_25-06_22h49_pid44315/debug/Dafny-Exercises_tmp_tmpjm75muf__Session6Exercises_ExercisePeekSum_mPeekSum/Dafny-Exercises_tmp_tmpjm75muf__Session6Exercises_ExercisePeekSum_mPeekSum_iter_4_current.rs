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
        v[n-1] + peekSum(v, n-1)
    }
}

// Helper lemma to prove the relationship between peekSum values
proof fn lemma_peekSum_step(v: Vec<int>, n: nat)
    requires
        0 < n <= v.len()
    ensures
        peekSum(v, n) == v[n-1] + peekSum(v, n-1)
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

// Helper lemma for the inductive step in the loop
proof fn lemma_peekSum_increment(v: Vec<int>, i: nat)
    requires
        i < v.len()
    ensures
        peekSum(v, i+1) == peekSum(v, i) + v[i as int]
{
    if i + 1 > 0 {
        lemma_peekSum_step(v, i+1);
        // peekSum(v, i+1) == v[(i+1)-1] + peekSum(v, (i+1)-1)
        // which is v[i] + peekSum(v, i)
    }
}

fn mPeekSum(v: Vec<int>) -> (sum: int)
    requires
        v.len() > 0
    ensures
        sum == peekSum(v, v.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    // Establish initial invariant
    proof {
        lemma_peekSum_zero(v);
    }
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == peekSum(v, i)
    {
        proof {
            lemma_peekSum_increment(v, i);
        }
        
        sum = sum + v[i as int];
        i = i + 1;
    }
    
    sum
}

}