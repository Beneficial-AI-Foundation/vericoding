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
        
        if n == 2 {
            return true;
        }
        
        if n % 2 == 0 {
            return false;
        }
        
        let mut i = 3u64;
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        while i * i <= n
            invariant 
                i >= 3,
                i % 2 == 1,
                forall|nr: nat| 2 <= nr < i ==> #[trigger] ((n as nat) % nr) != 0,
                forall|nr: nat| 1 < nr < (n as nat) && nr >= i ==> nr * nr > (n as nat)
            decreases n - i + 1
        {
            if n % i == 0 {
                proof {
                    assert((n as nat) % (i as nat) == 0);
                    assert(1 < (i as nat) < (n as nat));
                }
                return false;
            }
            i += 2;
        }
        
        proof {
            assert(forall|nr: nat| 1 < nr < (n as nat) ==> {
                if nr < i {
                    ((n as nat) % nr) != 0
                } else {
                    nr * nr > (n as nat) && ((n as nat) % nr) != 0
                }
            });
        }
        
        true
    }

    fn main() {
        /* code modified by LLM (iteration 1): moved test calls out of proof block to exec mode */
        // Test some prime numbers
        let result1 = test_primeness(2);
        let result2 = test_primeness(3);
        let result3 = test_primeness(5);
        let result4 = test_primeness(7);
        let result5 = test_primeness(4);
        let result6 = test_primeness(9);
        let result7 = test_primeness(15);
    }
}