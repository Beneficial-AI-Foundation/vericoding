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
        while i * i <= n
            invariant 
                i >= 3,
                i % 2 == 1,
                forall|nr: nat| 2 <= nr < i ==> #[trigger] (n % nr) != 0
        {
            if n % i == 0 {
                return false;
            }
            i += 2;
        }
        
        true
    }

    fn main() {
        // Test some prime numbers
        assert(test_primeness(2));
        assert(test_primeness(3));
        assert(test_primeness(5));
        assert(test_primeness(7));
        assert(!test_primeness(4));
        assert(!test_primeness(9));
        assert(!test_primeness(15));
    }
}