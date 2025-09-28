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
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn test_primeness(n: nat) -> (result: bool) 
      requires n >= 0,
      ensures result <==> prime(n),
// </vc-spec>
// <vc-code>
{
    if n <= 1 {
        assert(!prime(n));
        false
    } else {
        let mut i: nat = 2;
        while i < n
            invariant { 2 <= i && i <= n }
            invariant { forall|j: nat| 2 <= j < i ==> #[trigger] n % j != 0 }
            decreases { n - i }
        {
            if n % i == 0 {
                assert(1 < i && i < n);
                assert(n % i == 0);
                assert(!prime(n));
                return false;
            }
            i = i + 1;
        }
        assert(i == n);
        assert(forall|j: nat| 2 <= j < n ==> #[trigger] n % j != 0);
        assert(forall|nr: nat| 1 < nr < n ==> #[trigger] (n % nr) != 0);
        assert(prime(n));
        true
    }
}
// </vc-code>

fn main() {}

}