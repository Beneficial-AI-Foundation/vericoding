// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn prime(n: nat) -> bool {
    n > 1 && (forall|nr: nat| 1 < nr < n ==> #[trigger] (n % nr) != 0)
}

#[derive(PartialEq, Eq)]
enum Answer {
    Yes,
    No,
    Unknown,
}

struct PrimeMap {
    database: Ghost<Map<nat, bool>>,
}

impl PrimeMap {

    spec fn valid(&self) -> bool {
        forall|i: nat| self.database@.dom().contains(i) ==> (self.database@[i] == prime(i))
    }

    fn new() -> (result: PrimeMap)
        ensures 
            result.database@ === Map::empty(),
            result.valid(),
    {
        PrimeMap {
            database: Ghost(Map::empty())
        }
    }

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

}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using an 'implies' proof block */
proof fn forall_preserves(n: nat, i: nat)
    requires
        2 <= i < n,
        forall|d: nat| 2 <= d < i ==> (n % d) != 0,
        n % i != 0,
    ensures
        forall|d: nat| 2 <= d < i + 1 ==> (n % d) != 0,
{
    forall|d: nat| 2 <= d < i + 1 implies #[trigger]((n % d) != 0)
    {
        if d < i {
            // This case is covered by the precondition: forall|d: nat| 2 <= d < i ==> (n % d) != 0
        } else {
            // Here d >= i. With d < i + 1, this means d == i.
            // This case is covered by the precondition: n % i != 0
            assert(d == i);
        }
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
    /* code modified by LLM (iteration 5): no changes needed, as the compilation error was in the helper function */
    if n < 2 {
        proof {
            assert(!prime(n));
        }
        return false;
    }

    let mut i: nat = 2;
    while i < n
        invariant
            n >= 2,
            2 <= i <= n,
            forall|d: nat| 2 <= d < i ==> n % d != 0,
        decreases n - i
    {
        if n % i == 0 {
            proof {
                assert(1 < i < n);
                assert(!prime(n));
            }
            return false;
        }
        
        proof {
            forall_preserves(n, i);
        }
        i = i + 1;
    }

    proof {
        assert(prime(n));
    }
    true
}
// </vc-code>

}
fn main() {}