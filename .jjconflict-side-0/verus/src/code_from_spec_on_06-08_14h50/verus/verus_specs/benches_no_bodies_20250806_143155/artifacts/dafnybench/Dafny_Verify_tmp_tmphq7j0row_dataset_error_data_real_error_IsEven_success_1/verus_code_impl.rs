use vstd::prelude::*;

verus! {
    spec fn even(n: int) -> bool 
        recommends n >= 0
        decreases n
    {
        if n == 0 { 
            true 
        } else if n > 0 { 
            !even(n - 1) 
        } else {
            arbitrary()
        }
    }

    fn is_even(n: u32) -> (r: bool)
        requires n >= 0,
        ensures r <==> even(n as int)
    {
        proof {
            lemma_even_equivalent_mod2(n as int);
        }
        n % 2 == 0
    }

    proof fn lemma_even_equivalent_mod2(n: int)
        requires n >= 0
        ensures even(n) <==> (n % 2 == 0)
        decreases n
    {
        if n == 0 {
            // Base case: even(0) = true and 0 % 2 == 0
        } else if n == 1 {
            // Base case: even(1) = !even(0) = false and 1 % 2 == 1
        } else {
            // Inductive case: even(n) = !even(n-1)
            lemma_even_equivalent_mod2(n - 1);
            assert(even(n - 1) <==> ((n - 1) % 2 == 0));
            assert(even(n) == !even(n - 1));
            
            // Mathematical fact about modulo
            if (n - 1) % 2 == 0 {
                assert(n % 2 == 1);
            } else {
                assert(n % 2 == 0);
            }
        }
    }
}

fn main() {}