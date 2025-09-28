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
// Helper lemma to establish that if we've checked all divisors up to n-1 and found none,
// then n is prime
proof fn checked_all_divisors_implies_prime(n: nat, checked_up_to: nat)
    requires
        n > 1,
        checked_up_to == n,
        forall|nr: nat| 1 < nr < checked_up_to ==> #[trigger] (n % nr) != 0,
    ensures
        prime(n),
{
    assert forall|nr: nat| 1 < nr < n implies #[trigger] (n % nr) != 0 by {
        assert(nr < checked_up_to);
    }
}

// Helper lemma for when we find a divisor
proof fn found_divisor_not_prime(n: nat, divisor: nat)
    requires
        n > 1,
        1 < divisor < n,
        n % divisor == 0,
    ensures
        !prime(n),
{
    // This directly contradicts the prime definition
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
        return false;
    }
    
    let mut i: nat = 2;
    
    while i < n
        invariant
            2 <= i <= n,
            n > 1,
            forall|nr: nat| 1 < nr < i ==> #[trigger] (n % nr) != 0,
    {
        if n % i == 0 {
            proof {
                found_divisor_not_prime(n, i);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        checked_all_divisors_implies_prime(n, i);
    }
    true
}
// </vc-code>

fn main() {}

}