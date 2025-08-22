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
            assert(exp(x, 0) == 1);
        } else {
            // Inductive case: exp(x, e) = x * exp(x, e-1)
            // Since x > 0 and by induction exp(x, e-1) > 0, their product is positive
            exp_positive_property(x, e - 1);
            assert(exp(x, e - 1) > 0);
            assert(exp(x, e) == x * exp(x, e - 1));
        }
    }

    proof fn exp3_lemma(n: int) 
        requires n >= 1,
        ensures (exp(3, n) - 1) % 2 == 0,
        decreases n
    {
        if n == 1 {
            // Base case: exp(3, 1) = 3, so (3 - 1) = 2, and 2 % 2 = 0
            assert(exp(3, 1) == 3);
            /* code modified by LLM (iteration 1): added explicit int type annotation to fix compilation error */
            assert((exp(3, 1) - 1) % 2 == 2int % 2);
            assert(2int % 2 == 0);
        } else {
            // Inductive case: exp(3, n) = 3 * exp(3, n-1)
            // So exp(3, n) - 1 = 3 * exp(3, n-1) - 1 = 3 * (exp(3, n-1) - 1) + 3 - 1
            // = 3 * (exp(3, n-1) - 1) + 2
            // Since exp(3, n-1) - 1 is even (by induction), 3 * (even number) is even
            // And even + 2 is even
            exp3_lemma(n - 1);
            assert((exp(3, n - 1) - 1) % 2 == 0);
            assert(exp(3, n) == 3 * exp(3, n - 1));
            
            // exp(3, n) - 1 = 3 * exp(3, n-1) - 1 = 3 * exp(3, n-1) - 3 + 2
            // = 3 * (exp(3, n-1) - 1) + 2
            let prev = exp(3, n - 1) - 1;
            assert(prev % 2 == 0); // inductive hypothesis
            assert(exp(3, n) - 1 == 3 * prev + 2);
            // Since prev is even, 3 * prev is even, and even + even = even
            /* code modified by LLM (iteration 1): added explicit int type annotation to fix compilation error */
            assert((3 * prev + 2int) % 2 == (3 * prev) % 2 + 2int % 2);
        }
    }

    proof fn mult8_lemma(n: int)
        requires n >= 1,
        ensures (exp(3, 2 * n) - 1) % 8 == 0,
        decreases n
    {
        if n == 1 {
            // Base case: exp(3, 2) = 9, so (9 - 1) = 8, and 8 % 8 = 0
            assert(exp(3, 2) == exp(3, 1) * 3);
            assert(exp(3, 1) == 3);
            assert(exp(3, 2) == 9);
            /* code modified by LLM (iteration 1): added explicit int type annotation to fix compilation error */
            assert((exp(3, 2) - 1) % 8 == 8int % 8);
            assert(8int % 8 == 0);
        } else {
            // Inductive case
            mult8_lemma(n - 1);
            assert((exp(3, 2 * (n - 1)) - 1) % 8 == 0);
            
            // exp(3, 2*n) = exp(3, 2*(n-1) + 2) = exp(3, 2*(n-1)) * exp(3, 2)
            // = exp(3, 2*(n-1)) * 9
            assert(exp(3, 2 * n) == exp(3, 2 * (n - 1)) * exp(3, 2));
            assert(exp(3, 2) == 9);
            assert(exp(3, 2 * n) == exp(3, 2 * (n - 1)) * 9);
            
            // So exp(3, 2*n) - 1 = exp(3, 2*(n-1)) * 9 - 1
            // = exp(3, 2*(n-1)) * 9 - 9 + 8
            // = 9 * (exp(3, 2*(n-1)) - 1) + 8
            let prev = exp(3, 2 * (n - 1)) - 1;
            assert(prev % 8 == 0); // inductive hypothesis
            assert(exp(3, 2 * n) - 1 == 9 * prev + 8);
            
            // Since prev ≡ 0 (mod 8), we have 9 * prev ≡ 0 (mod 8)
            // So 9 * prev + 8 ≡ 0 + 0 ≡ 0 (mod 8)
            /* code modified by LLM (iteration 1): added explicit int type annotation to fix compilation error */
            assert((9 * prev + 8int) % 8 == (9 * prev) % 8 + 8int % 8);
            assert(8int % 8 == 0);
        }
    }
}

fn main() {}