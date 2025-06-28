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

// Helper lemma for the inductive step in the loop
proof fn lemma_peekSum_increment(v: Vec<int>, i: nat)
    requires
        i < v.len()
    ensures
        peekSum(v, (i+1) as nat) == peekSum(v, i) + v[i as int]
{
    // We need to prove that peekSum(v, i+1) == peekSum(v, i) + v[i]
    // By definition: peekSum(v, i+1) = v[i] + peekSum(v, i)
    // So we need to show commutativity: v[i] + peekSum(v, i) == peekSum(v, i) + v[i]
    
    if i + 1 <= v.len() {
        // peekSum(v, i+1) = v[(i+1)-1] + peekSum(v, (i+1)-1) = v[i] + peekSum(v, i)
        assert(peekSum(v, (i+1) as nat) == v[i as int] + peekSum(v, i));
        // Addition is commutative
        assert(v[i as int] + peekSum(v, i) == peekSum(v, i) + v[i as int]);
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
        proof {
            lemma_peekSum_increment(v, i as nat);
        }
        
        sum = sum + v[i as int];
        i = i + 1;
    }
    
    sum
}

}