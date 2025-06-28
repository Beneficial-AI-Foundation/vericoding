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
        // Use the fact that addition is commutative
        assert(sumTo(a, n) == a[(n - 1) as int] + sumTo(a, n - 1));
        assert(sumUpTo(a, n) == sumUpTo(a, n - 1) + a[(n - 1) as int]);
        assert(sumTo(a, n - 1) == sumUpTo(a, n - 1)); // inductive hypothesis
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
            sum == sumUpTo(a, i as nat),
    {
        proof {
            // Help Verus understand the step
            let old_i = i;
            assert(sumUpTo(a, (old_i + 1) as nat) == sumUpTo(a, old_i as nat) + a[old_i as int]) by {
                // This follows from the definition of sumUpTo
                assert((old_i + 1) as nat > 0);
                assert(sumUpTo(a, (old_i + 1) as nat) == sumUpTo(a, ((old_i + 1) - 1) as nat) + a[((old_i + 1) - 1) as int]);
                assert(((old_i + 1) - 1) as nat == old_i as nat);
                assert(((old_i + 1) - 1) as int == old_i as int);
            };
        }
        sum = sum + a[i as int];
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