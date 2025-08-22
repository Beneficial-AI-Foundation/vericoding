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
                forall|k: nat| 2 <= k < i ==> #[trigger] (n % k) != 0
        {
            if n % i == 0 {
                return false;
            }
            i = i + 1;
        }
        
        true
    }

    fn main() {
    }
}