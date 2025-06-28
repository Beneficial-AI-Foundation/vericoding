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
        sum = sum + a[i as int];
        i = i + 1;
        
        proof {
            // Prove that the invariant is maintained
            let old_sum = sum - a[(i - 1) as int];
            let old_i = i - 1;
            
            assert(old_sum == sumUpTo(a, old_i as nat));
            assert(sum == old_sum + a[old_i as int]);
            
            // Show that this equals sumUpTo(a, i as nat)
            assert(i as nat > 0);
            assert(sumUpTo(a, i as nat) == sumUpTo(a, (i - 1) as nat) + a[(i - 1) as int]) by {
                // This follows from the definition of sumUpTo
                assert(sumUpTo(a, i as nat) == sumUpTo(a, i as nat - 1) + a[(i as nat - 1) as int]);
                assert(i as nat - 1 == (i - 1) as nat);
                assert((i as nat - 1) as int == (i - 1) as int);
            };
            
            assert(sum == sumUpTo(a, i as nat));
        }
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