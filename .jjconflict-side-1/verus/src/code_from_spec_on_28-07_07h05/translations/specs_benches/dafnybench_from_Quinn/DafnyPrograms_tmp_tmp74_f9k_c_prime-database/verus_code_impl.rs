use vstd::prelude::*;

verus! {
    // Predicate for primeness
    spec fn prime(n: nat) -> bool {
        n > 1 && (forall|nr: nat| 1 < nr < n ==> #[trigger] (n % nr) != 0)
    }

    // Datatype for Answer
    #[derive(PartialEq, Eq)]
    enum Answer {
        Yes,
        No,
        Unknown,
    }

    // Method to test whether a number is prime, returns bool
    fn test_primeness(n: u64) -> (result: bool)
        ensures result == prime(n as nat)
    {
        if n <= 1 {
            /* code modified by LLM (iteration 1): Added assertion to prove postcondition for base case */
            assert(!prime(n as nat));
            return false;
        }
        
        let mut i = 2u64;
        /* code modified by LLM (iteration 1): Strengthened loop invariant to establish postcondition */
        while i < n
            invariant 
                2 <= i <= n,
                n > 1,
                forall|nr: nat| 2 <= nr < i ==> #[trigger] ((n as nat) % nr) != 0,
            decreases n - i
        {
            if n % i == 0 {
                /* code modified by LLM (iteration 1): Added assertion to prove n is not prime when divisor found */
                assert(1 < (i as nat) < (n as nat));
                assert((n as nat) % (i as nat) == 0);
                assert(!prime(n as nat));
                return false;
            }
            i = i + 1;
        }
        
        /* code modified by LLM (iteration 1): Added assertions to prove n is prime when no divisors found */
        assert(i == n);
        assert(forall|nr: nat| 2 <= nr < (n as nat) ==> #[trigger] ((n as nat) % nr) != 0);
        assert(forall|nr: nat| 1 < nr < (n as nat) ==> #[trigger] ((n as nat) % nr) != 0);
        assert(prime(n as nat));
        return true;
    }

    fn main() {
        let test_cases = [2u64, 3u64, 4u64, 17u64, 25u64];
        let mut idx = 0;
        
        /* code modified by LLM (iteration 1): Added decreases clause for main loop */
        while idx < test_cases.len()
            decreases test_cases.len() - idx
        {
            let n = test_cases[idx];
            let is_prime = test_primeness(n);
            idx = idx + 1;
        }
    }
}