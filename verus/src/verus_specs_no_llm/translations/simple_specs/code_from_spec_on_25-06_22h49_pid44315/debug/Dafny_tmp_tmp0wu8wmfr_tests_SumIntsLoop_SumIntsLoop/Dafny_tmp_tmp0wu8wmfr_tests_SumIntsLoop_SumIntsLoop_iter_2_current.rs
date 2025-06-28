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
    } else {
        // Inductive step
        lemma_sum_formula(n - 1);
        // sumInts(n) = n + sumInts(n-1) = n + (n-1)*n/2 = n*(n+1)/2
        assert(sumInts(n) == n + sumInts(n - 1));
        assert(sumInts(n - 1) == (n - 1) * n / 2);
        assert(sumInts(n) == n + (n - 1) * n / 2);
        assert(sumInts(n) == (2 * n + (n - 1) * n) / 2);
        assert(sumInts(n) == (2 * n + n * n - n) / 2);
        assert(sumInts(n) == (n + n * n) / 2);
        assert(sumInts(n) == n * (1 + n) / 2);
        assert(sumInts(n) == n * (n + 1) / 2);
    }
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
    let mut sum = 0;
    let mut i = 0;
    
    while i <= n
        invariant
            0 <= i <= n + 1,
            sum == sumInts(i - 1),
    {
        sum = sum + i;
        i = i + 1;
    }
    
    // Prove the final relationship using the lemma
    proof {
        lemma_sum_formula(n);
    }
    
    sum
}

}