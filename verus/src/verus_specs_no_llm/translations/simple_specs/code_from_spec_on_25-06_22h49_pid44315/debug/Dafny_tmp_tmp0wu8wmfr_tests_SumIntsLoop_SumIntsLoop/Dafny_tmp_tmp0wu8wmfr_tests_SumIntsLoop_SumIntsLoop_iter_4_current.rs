use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to define the sum of integers from 0 to n
spec fn sumInts(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        n + sumInts(n - 1)
    }
}

// Helper lemma to prove the mathematical relationship
proof fn lemma_sum_formula(n: int)
    requires n >= 0
    ensures sumInts(n) == n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        // Base case: sumInts(0) = 0 = 0 * 1 / 2
        assert(sumInts(0) == 0);
        assert(0 * (0 + 1) / 2 == 0);
    } else {
        // Inductive step
        lemma_sum_formula(n - 1);
        assert(sumInts(n) == n + sumInts(n - 1));
        assert(sumInts(n - 1) == (n - 1) * n / 2);
        
        // More careful arithmetic reasoning
        assert(sumInts(n) == n + (n - 1) * n / 2);
        assert(n + (n - 1) * n / 2 == (2 * n + (n - 1) * n) / 2);
        assert((2 * n + (n - 1) * n) / 2 == (2 * n + n * n - n) / 2);
        assert((2 * n + n * n - n) / 2 == (n + n * n) / 2);
        assert((n + n * n) / 2 == n * (1 + n) / 2);
        assert(n * (1 + n) / 2 == n * (n + 1) / 2);
    }
}

// Helper lemma for the loop invariant
proof fn lemma_sumInts_step(i: int)
    requires i >= 1
    ensures sumInts(i) == sumInts(i - 1) + i
{
    // This follows directly from the definition of sumInts
}

fn main() {
}

fn SumIntsLoop(n: int) -> (s: int)
    requires
        n >= 0
    ensures
        s == sumInts(n),
        s == n*(n+1)/2
{
    if n == 0 {
        proof {
            lemma_sum_formula(0);
        }
        return 0;
    }
    
    let mut sum = 0;
    let mut i = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum == sumInts(i - 1),
            n >= 1,
    {
        proof {
            lemma_sumInts_step(i);
        }
        sum = sum + i;
        i = i + 1;
    }
    
    // After the loop, i == n + 1, so sum == sumInts(n)
    assert(i == n + 1);
    assert(sum == sumInts(n));
    
    // Prove the final relationship using the lemma
    proof {
        lemma_sum_formula(n);
    }
    
    sum
}

}