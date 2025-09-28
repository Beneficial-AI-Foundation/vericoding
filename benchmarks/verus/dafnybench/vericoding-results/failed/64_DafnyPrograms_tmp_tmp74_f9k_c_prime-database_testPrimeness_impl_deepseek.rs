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
spec fn divides(a: nat, b: nat) -> bool {
    b % a == 0
}

spec fn has_no_divisor_in(n: nat, start: nat, end: nat) -> bool {
    forall|d: nat| start <= d < end ==> #[trigger] !divides(d, n)
}

proof fn prime_characterization(n: nat)
    ensures
        prime(n) <==> (n > 1 && has_no_divisor_in(n, 2, n)),
{
}

proof fn prime_check_lemma(n: nat, d: nat)
    requires
        n > 1,
        2 <= d <= n - 1,
        forall|div: nat| 2 <= div < d ==> #[trigger] !divides(div, n),
    ensures
        has_no_divisor_in(n, 2, d) && #[trigger] !divides(d, n) ==> has_no_divisor_in(n, 2, d + 1),
{
}

proof fn nat_le_one_implies_not_prime(n: nat)
    ensures
        n <= 1 ==> !prime(n),
{
}

proof fn nat_to_int_lemma(n: nat)
    ensures
        n as int >= 0,
{
}

proof fn nat_comparison_lemma(a: nat, b: nat)
    ensures
        a < b <==> (a as int) < (b as int),
        a <= b <==> (a as int) <= (b as int),
{
}

proof fn nat_add_one_lemma(a: nat)
    ensures
        (a + 1) as int == a as int + 1,
{
}

proof fn nat_sub_lemma(a: nat, b: nat)
    requires a >= b,
    ensures
        (a - b) as int == a as int - b as int,
{
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
            nat_le_one_implies_not_prime(n);
        }
        false
    } else {
        let mut d: nat = 2;
        proof {
            nat_to_int_lemma(d);
            nat_to_int_lemma(n);
            nat_comparison_lemma(d, n);
        }
        while d < n
            invariant
                2 <= d <= n,
                has_no_divisor_in(n, 2, d),
            decreases n - d,
        {
            let remainder: nat = n % d;
            if remainder == 0 {
                proof {
                    assert(divides(d, n));
                    assert(!has_no_divisor_in(n, 2, n));
                    assert(!prime(n)) by {
                        prime_characterization(n);
                    }
                }
                return false;
            }
            proof {
                prime_check_lemma(n, d);
            }
            d = d + 1;
            proof {
                nat_to_int_lemma(d);
                nat_to_int_lemma(n);
                nat_comparison_lemma(d, n);
            }
        }
        proof {
            assert(has_no_divisor_in(n, 2, n));
            prime_characterization(n);
            assert(prime(n));
        }
        true
    }
}
// </vc-code>

fn main() {}

}