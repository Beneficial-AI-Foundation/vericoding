use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumTo(a: Vec<int>, n: nat) -> int
    recommends n <= a.len()
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
    recommends n <= a.len()
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
        // Both functions compute the same sum, just in different orders
        assert(sumTo(a, n) == a[(n - 1) as int] + sumTo(a, n - 1));
        assert(sumUpTo(a, n) == sumUpTo(a, n - 1) + a[(n - 1) as int]);
        // By inductive hypothesis: sumTo(a, n-1) == sumUpTo(a, n-1)
        // Therefore: a[(n-1)] + sumTo(a, n-1) == sumUpTo(a, n-1) + a[(n-1)]
        assert(sumTo(a, n - 1) == sumUpTo(a, n - 1));
        assert(a[(n - 1) as int] + sumTo(a, n - 1) == sumUpTo(a, n - 1) + a[(n - 1) as int]);
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
            sum == sumUpTo(a, i as nat)
    {
        proof {
            // Before adding a[i], we have sum == sumUpTo(a, i)
            // After adding a[i], we want sum == sumUpTo(a, i+1)
            assert(i < a.len());
            assert((i + 1) as nat <= a.len());
            // Key insight: sumUpTo builds the sum by adding elements from left to right
            // sumUpTo(a, i+1) = sumUpTo(a, i) + a[i]
            assert(sumUpTo(a, (i + 1) as nat) == sumUpTo(a, i as nat) + a[i as int]);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    // Prove that the final result matches the required specification
    proof {
        assert(i == a.len());
        assert(sum == sumUpTo(a, a.len()));
        lemma_sum_equivalence(a, a.len());
        assert(sumUpTo(a, a.len()) == sumTo(a, a.len()));
    }
    
    sum
}

}