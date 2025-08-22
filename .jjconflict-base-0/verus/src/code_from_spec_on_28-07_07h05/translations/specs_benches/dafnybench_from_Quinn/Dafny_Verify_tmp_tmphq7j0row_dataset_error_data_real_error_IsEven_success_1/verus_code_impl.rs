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

    /* code modified by LLM (iteration 3): Fixed compilation errors - added type annotations and fixed chained comparisons */
    proof fn lemma_even_mod_equiv(n: nat)
        ensures even(n as int) <==> (n % 2 == 0)
        decreases n
    {
        if n == 0 {
            // Base case: even(0) is true and 0 % 2 == 0
            assert(even(0int) == true);
            assert(0nat % 2 == 0);
        } else if n == 1 {
            // Base case: even(1) is false and 1 % 2 == 1
            assert(even(1int) == !even(0int));
            assert(!even(0int) == false);
            assert(1nat % 2 == 1);
        } else {
            // Inductive case: use the fact that even(n) == !even(n-1)
            lemma_even_mod_equiv((n - 1) as nat);
            // We know: even((n-1) as int) <==> ((n-1) % 2 == 0)
            // We need to show: even(n as int) <==> (n % 2 == 0)
            // Since even(n) == !even(n-1), we have:
            // even(n) <==> !even(n-1) <==> !((n-1) % 2 == 0) <==> ((n-1) % 2 == 1)
            // And ((n-1) % 2 == 1) <==> (n % 2 == 0) by modular arithmetic
            assert(even(n as int) == !even((n - 1) as int));
            assert(((n - 1) % 2 == 0) ==> (n % 2 == 1));
            assert(((n - 1) % 2 == 1) ==> (n % 2 == 0));
        }
    }

    fn is_even(n: u32) -> (r: bool)
        requires n >= 0,
        ensures r <==> even(n as int)
    {
        /* code modified by LLM (iteration 3): Added proof to establish equivalence */
        proof {
            lemma_even_mod_equiv(n as nat);
        }
        n % 2 == 0
    }
}

fn main() {}