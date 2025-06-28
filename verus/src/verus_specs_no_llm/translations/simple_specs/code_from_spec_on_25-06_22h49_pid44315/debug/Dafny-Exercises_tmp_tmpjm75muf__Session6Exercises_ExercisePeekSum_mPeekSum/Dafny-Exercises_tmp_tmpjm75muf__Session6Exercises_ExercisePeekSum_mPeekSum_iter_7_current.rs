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
    // The ensures clause matches the recursive case definition
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
        peekSum(v, (i+1) as nat) == peekSum(v, i) + v[i as int]
{
    // We prove by showing the recursive expansion
    if (i + 1) <= v.len() {
        // By definition of peekSum:
        // peekSum(v, i+1) = v[(i+1)-1] + peekSum(v, (i+1)-1)
        //                 = v[i] + peekSum(v, i)
        assert(peekSum(v, (i+1) as nat) == v[((i+1)-1) as int] + peekSum(v, ((i+1)-1) as nat));
        assert(((i+1)-1) as int == i as int);
        assert(((i+1)-1) as nat == i);
        // Therefore: peekSum(v, i+1) = v[i] + peekSum(v, i) = peekSum(v, i) + v[i]
    }
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
            lemma_peekSum_increment(v, i as nat);
            // After this lemma: peekSum(v, i+1) == peekSum(v, i) + v[i]
            // So: sum + v[i] == peekSum(v, i) + v[i] == peekSum(v, i+1)
        }
        
        sum = sum + v[i];
        i = i + 1;
        
        // At this point: sum == peekSum(v, i as nat) holds for the new i
    }
    
    // When loop exits: i == v.len() and sum == peekSum(v, i as nat) == peekSum(v, v.len())
    sum
}

}