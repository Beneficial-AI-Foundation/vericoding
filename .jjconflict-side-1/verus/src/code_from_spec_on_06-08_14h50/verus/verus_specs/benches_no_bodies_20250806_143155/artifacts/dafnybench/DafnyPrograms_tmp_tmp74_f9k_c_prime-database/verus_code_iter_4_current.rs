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
            return false;
        }
        
        let mut i = 2u64;
        while i < n
            invariant 
                2 <= i <= n,
                forall|k: nat| 2 <= k < i ==> #[trigger] ((n as nat) % k) != 0
            decreases n - i
        {
            if n % i == 0 {
                /* code modified by LLM (iteration 2): Added trigger annotation to exists quantifier and simplified proof */
                proof {
                    assert((n as nat) % (i as nat) == 0);
                    assert(1 < i < n);
                    assert(exists|nr: nat| 1 < nr < n && #[trigger] ((n as nat) % nr) == 0 by {
                        assert(1 < (i as nat) < (n as nat));
                        assert((n as nat) % (i as nat) == 0);
                    });
                }
                return false;
            }
            i = i + 1;
        }
        
        /* code modified by LLM (iteration 2): Simplified proof block for primeness case */
        proof {
            assert(i == n);
            assert(forall|k: nat| 2 <= k < n ==> (n as nat) % k != 0);
            assert(forall|nr: nat| 1 < nr < n ==> (n as nat) % nr != 0);
        }
        true
    }

    fn main() {
    }
}