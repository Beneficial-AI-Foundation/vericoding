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
// Helper function to check if a number is prime by trial division
fn is_prime_trial_division(n: nat) -> (result: bool)
    requires n >= 0,
    ensures result <==> prime(n),
{
    if n <= 1 {
        false
    } else if n == 2 {
        true
    } else {
        let mut i: nat = 2;
        while i < n
            invariant 
                2 <= i <= n,
                forall|k: nat| 2 <= k < i ==> #[trigger] (n % k) != 0,
        {
            if n % i == 0 {
                assert(n % i == 0 && 1 < i < n);
                assert(!prime(n));
                return false;
            }
            i = i + 1;
        }
        assert(forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0);
        assert(forall|k: nat| 1 < k < n ==> #[trigger] (n % k) != 0);
        true
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
    is_prime_trial_division(n)
}
// </vc-code>

fn main() {}

}