use vstd::prelude::*;

verus! {

// predicate for primeness
spec fn prime(n: nat) -> bool {
    n > 1 && (forall|nr: nat| 1 < nr < n ==> #[trigger] (n % nr) != 0)
}

#[derive(PartialEq, Eq)]
enum Answer {
    Yes,
    No,
    Unknown,
}

// the class containing a prime database, if a number is prime it returns Yes, if it is not No and if the number
// is not in the database it returns Unknown
struct PrimeMap {
    database: Ghost<Map<nat, bool>>,
}

impl PrimeMap {
    // the valid invariant of the class
    spec fn valid(&self) -> bool {
        forall|i: nat| self.database@.dom().contains(i) ==> (self.database@[i] == prime(i))
    }

    // the constructor
    fn new() -> (result: PrimeMap)
        ensures 
            result.database@ === Map::empty(),
            result.valid(),
    {
        PrimeMap {
            database: Ghost(Map::empty())
        }
    }

    // lookup n in the database and reply with Yes or No if it's in the database and it is or it is not prime,
    // or with Unknown when it's not in the databse
    fn is_prime(&self, n: nat) -> (answer: Answer)
        requires self.valid(),
        ensures 
            self.database@.dom().contains(n) && prime(n) <==> answer == Answer::Yes,
            self.database@.dom().contains(n) && !prime(n) <==> answer == Answer::No,
            !self.database@.dom().contains(n) <==> answer == Answer::Unknown,
    {
        assume(false);
        Answer::Unknown
    }

    // method to test whether a number is prime, returns bool

}

// <vc-helpers>
spec fn is_prime_test(n: nat) -> (result: bool) {
    if n <= 1 {
        false
    } else {
        !exists|i: nat| 2 <= i < n && n % i == 0
    }
}
// </vc-helpers>

// <vc-spec>
fn test_primeness(n: nat) -> (result: bool) 
      requires n >= 0,
      ensures result <==> prime(n),
// </vc-spec>
// <vc-code>
{
    if n <= 1 {
        proof {
            // prime(n) is defined as n > 1 && ...
            // If n <= 1, then n > 1 is false, so prime(n) is false.
            assert(!prime(n));
        }
        false
    } else {
        let mut i: nat = 2;
        let mut is_n_prime: bool = true;

        while (i < n) && is_n_prime
            invariant
                2 <= i,
                i <= n,
                is_n_prime == (forall|d: nat| 2 <= d < i ==> n % d != 0),
            decreases n - i
        {
            if n % i == 0 {
                is_n_prime = false;
            }
            i = i + 1;
        }

        proof {
            if is_n_prime {
                assert(n > 1);
                assert(i == n); // The loop terminates because i eventually reaches n or is_n_prime becomes false.
                                // Since is_n_prime is true, i must have become n.
                                // So any 'nr' such that 1 < nr < n would have been checked.
                assert(forall|nr: nat| 1 < nr < n ==> n % nr != 0);
                assert(prime(n));
            } else {
                // If is_n_prime is false, it means at some point in the loop, n % i == 0 for some 'i'.
                // Let prev_is_n_prime be the value of is_n_prime at the start of the current iteration.
                // If is_n_prime became false, it means that `is_n_prime_old` was true and `n % i_old == 0`.
                // The invariant `is_n_prime == (forall|d: nat| 2 <= d < i ==> n % d != 0)` tells us that
                // if `is_n_prime` is false, there exists `d_0` such that `2 <= d_0 < i` and `n % d_0 == 0`.
                // The final value of `i` after the loop will be one greater than the `i` at which `is_n_prime` became false.
                // This `d_0` violates the `prime` predicate.
                 assert(!prime(n));
            }
        }
        is_n_prime
    }
}
// </vc-code>

fn main() {}

}