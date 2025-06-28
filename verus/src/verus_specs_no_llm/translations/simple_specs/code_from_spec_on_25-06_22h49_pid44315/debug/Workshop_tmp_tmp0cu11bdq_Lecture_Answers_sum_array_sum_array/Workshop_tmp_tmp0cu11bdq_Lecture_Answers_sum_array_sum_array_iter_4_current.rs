use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumTo(a: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        a[(n - 1) as int] + sumTo(a, n - 1)
    }
}

// Helper spec function that sums from 0 to n-1 (matching loop behavior)
spec fn sumUpTo(a: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sumUpTo(a, n - 1) + a[(n - 1) as int]
    }
}

// Lemma to prove equivalence between sumTo and sumUpTo
proof fn lemma_sum_equivalence(a: Vec<int>, n: nat)
    requires n <= a.len()
    ensures sumTo(a, n) == sumUpTo(a, n)
    decreases n
{
    if n == 0 {
        // Base case: both return 0
    } else {
        // Inductive step
        lemma_sum_equivalence(a, n - 1);
    }
}

fn sum_array(a: Vec<int>) -> (sum: int)
    ensures
        sum == sumTo(a, a.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sumUpTo(a, i)
    {
        sum = sum + a[i];
        i = i + 1;
    }
    
    // Prove that the final result matches the required specification
    proof {
        assert(a.len() <= a.len()); // This trivial assertion helps Verus see the precondition
        lemma_sum_equivalence(a, a.len());
    }
    
    sum
}

}