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
    ensures sumInts(n) * 2 == n * (n + 1)
    decreases n
{
    if n == 0 {
        // Base case: sumInts(0) * 2 = 0 * 2 = 0 = 0 * 1
        assert(sumInts(0) == 0);
        assert(sumInts(0) * 2 == 0);
        assert(0 * (0 + 1) == 0);
    } else {
        // Inductive step
        lemma_sum_formula(n - 1);
        assert(sumInts(n - 1) * 2 == (n - 1) * n);
        assert(sumInts(n) == n + sumInts(n - 1));
        assert(sumInts(n) * 2 == (n + sumInts(n - 1)) * 2);
        assert(sumInts(n) * 2 == n * 2 + sumInts(n - 1) * 2);
        assert(sumInts(n) * 2 == n * 2 + (n - 1) * n);
        assert(sumInts(n) * 2 == n * 2 + n * n - n);
        assert(sumInts(n) * 2 == n + n * n);
        assert(sumInts(n) * 2 == n * (n + 1));
    }
}

// Helper lemma for the loop invariant
proof fn lemma_sumInts_step(i: int)
    requires i >= 1
    ensures sumInts(i) == sumInts(i - 1) + i
{
    // This follows directly from the definition of sumInts
    assert(sumInts(i) == i + sumInts(i - 1));
}

// Lemma to prove that n*(n+1) is always even
proof fn lemma_even_product(n: int)
    requires n >= 0
    ensures (n * (n + 1)) % 2 == 0
{
    if n % 2 == 0 {
        // n is even, so n * (n + 1) is even
        assert((n * (n + 1)) % 2 == 0);
    } else {
        // n is odd, so (n + 1) is even, so n * (n + 1) is even
        assert(((n + 1) % 2) == 0);
        assert((n * (n + 1)) % 2 == 0);
    }
}

// Helper lemma to establish the division property
proof fn lemma_sum_division(n: int)
    requires n >= 0
    ensures sumInts(n) == n * (n + 1) / 2
{
    lemma_sum_formula(n);
    lemma_even_product(n);
    // Since sumInts(n) * 2 == n * (n + 1) and n * (n + 1) is even,
    // we have sumInts(n) == n * (n + 1) / 2
    assert(sumInts(n) * 2 == n * (n + 1));
    assert((n * (n + 1)) % 2 == 0);
    assert(sumInts(n) == n * (n + 1) / 2);
}

// Additional lemma to help with loop bounds
proof fn lemma_sumInts_bounds(n: int)
    requires n >= 0
    ensures sumInts(n) >= 0
    decreases n
{
    if n <= 0 {
        assert(sumInts(n) == 0);
    } else {
        lemma_sumInts_bounds(n - 1);
        assert(sumInts(n) == n + sumInts(n - 1));
        assert(sumInts(n) >= n);
        assert(sumInts(n) >= 0);
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
    if n == 0 {
        proof {
            lemma_sum_division(0);
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
    proof {
        assert(i == n + 1);
        assert(sum == sumInts(i - 1));
        assert(sum == sumInts(n));
        lemma_sum_division(n);
        assert(sumInts(n) == n * (n + 1) / 2);
        assert(sum == n * (n + 1) / 2);
    }
    
    sum
}

}