use vstd::prelude::*;

verus! {
    spec fn exp(x: int, e: int) -> int
        decreases e
    {
        if e >= 0 {
            if e == 0 { 1 } else { x * exp(x, e - 1) }
        } else {
            arbitrary() // undefined behavior for negative e
        }
    }

    // This proof function corresponds to the ensures clause in the original Dafny function
    proof fn exp_positive_property(x: int, e: int)
        requires x > 0, e >= 0,
        ensures exp(x, e) > 0,
        decreases e
    {
        if e == 0 {
            // Base case: exp(x, 0) = 1 > 0
        } else {
            // Inductive case: exp(x, e) = x * exp(x, e-1)
            // By inductive hypothesis, exp(x, e-1) > 0
            // Since x > 0, we have x * exp(x, e-1) > 0
            exp_positive_property(x, e - 1);
        }
    }

    proof fn exp3_lemma(n: int) 
        requires n >= 1,
        ensures (exp(3, n) - 1) % 2 == 0,
        decreases n
    {
        if n == 1 {
            // Base case: exp(3, 1) = 3, so (3 - 1) = 2, and 2 % 2 == 0
            assert(exp(3, 1) == 3);
            assert((exp(3, 1) - 1) == 2);
            assert(2 % 2 == 0);
        } else {
            // Inductive case: exp(3, n) = 3 * exp(3, n-1)
            // By inductive hypothesis, (exp(3, n-1) - 1) % 2 == 0
            // So exp(3, n-1) - 1 = 2k for some integer k
            // Therefore exp(3, n-1) = 2k + 1 (odd)
            // exp(3, n) = 3 * exp(3, n-1) = 3 * (2k + 1) = 6k + 3
            // exp(3, n) - 1 = 6k + 3 - 1 = 6k + 2 = 2(3k + 1)
            // So (exp(3, n) - 1) % 2 == 0
            exp3_lemma(n - 1);
        }
    }

    proof fn mult8_lemma(n: int)
        requires n >= 1,
        ensures (exp(3, 2 * n) - 1) % 8 == 0,
        decreases n
    {
        if n == 1 {
            // Base case: exp(3, 2) = 9, so (9 - 1) = 8, and 8 % 8 == 0
            assert(exp(3, 2) == 3 * exp(3, 1));
            assert(exp(3, 1) == 3);
            assert(exp(3, 2) == 9);
            assert((exp(3, 2) - 1) == 8);
            assert(8 % 8 == 0);
        } else {
            // Inductive case: exp(3, 2n) = exp(3, 2(n-1) + 2) = exp(3, 2(n-1)) * exp(3, 2)
            // = exp(3, 2(n-1)) * 9
            // By inductive hypothesis, (exp(3, 2(n-1)) - 1) % 8 == 0
            // So exp(3, 2(n-1)) - 1 = 8k for some integer k
            // Therefore exp(3, 2(n-1)) = 8k + 1
            // exp(3, 2n) = (8k + 1) * 9 = 72k + 9
            // exp(3, 2n) - 1 = 72k + 9 - 1 = 72k + 8 = 8(9k + 1)
            // So (exp(3, 2n) - 1) % 8 == 0
            mult8_lemma(n - 1);
            assert(exp(3, 2 * n) == exp(3, 2 * (n - 1) + 2));
            assert(exp(3, 2 * (n - 1) + 2) == exp(3, 2 * (n - 1)) * exp(3, 2));
            assert(exp(3, 2) == 9);
        }
    }
}

fn main() {}