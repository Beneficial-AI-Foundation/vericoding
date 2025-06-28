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
    // Since n > 0 and n <= v.len(), the condition n == 0 || n > v.len() is false
    // So we take the else branch: v[(n-1) as int] + peekSum(v, (n-1) as nat)
}

// Additional helper lemma for the base case
proof fn lemma_peekSum_zero(v: Vec<int>)
    ensures
        peekSum(v, 0) == 0
{
    // This follows directly from the definition of peekSum
    // When n == 0, the condition n == 0 || n > v.len() is true, so peekSum returns 0
}

// Helper lemma for out of bounds case
proof fn lemma_peekSum_out_of_bounds(v: Vec<int>, n: nat)
    requires
        n > v.len()
    ensures
        peekSum(v, n) == 0
{
    // When n > v.len(), the condition n == 0 || n > v.len() is true, so peekSum returns 0
}

// Helper lemma for the inductive step in the loop
proof fn lemma_peekSum_increment(v: Vec<int>, i: nat)
    requires
        i < v.len()
    ensures
        peekSum(v, (i+1) as nat) == peekSum(v, i) + v[i as int]
{
    // We need to prove this by induction on the structure of peekSum
    if i == 0 {
        // Base case: peekSum(v, 1) == peekSum(v, 0) + v[0]
        // peekSum(v, 1) = v[0] + peekSum(v, 0) = v[0] + 0 = v[0]
        // peekSum(v, 0) + v[0] = 0 + v[0] = v[0]
        lemma_peekSum_zero(v);
        lemma_peekSum_step(v, 1);
    } else {
        // Inductive case: assume it holds for i-1, prove for i
        // peekSum(v, i+1) = v[i] + peekSum(v, i)
        // peekSum(v, i) + v[i] = peekSum(v, i) + v[i]
        lemma_peekSum_step(v, (i+1) as nat);
        // The equation follows from commutativity of addition
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
            assert(i < v.len()); // From loop condition
            lemma_peekSum_increment(v, i as nat);
            // This gives us: peekSum(v, (i+1) as nat) == peekSum(v, i as nat) + v[i as int]
            // Since sum == peekSum(v, i as nat), we get:
            // peekSum(v, (i+1) as nat) == sum + v[i as int]
        }
        
        sum = sum + v[i];
        i = i + 1;
        
        // At this point: sum == peekSum(v, i as nat) holds for the new i
        // This is because:
        // - old sum == peekSum(v, old_i as nat)
        // - new sum = old sum + v[old_i] == peekSum(v, old_i as nat) + v[old_i as int]
        // - new i = old_i + 1
        // - By lemma_peekSum_increment: peekSum(v, (old_i+1) as nat) == peekSum(v, old_i as nat) + v[old_i as int]
        // - Therefore: new sum == peekSum(v, new_i as nat)
    }
    
    // When loop exits: i == v.len() and sum == peekSum(v, i as nat) == peekSum(v, v.len())
    sum
}

}