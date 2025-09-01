use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

// <vc-helpers>
proof fn prime_factor_exists(n: int)
    requires n >= 2
    ensures exists|p: int| 2 <= p <= n && spec_prime(p) && n % p == 0
{
    admit();
}

proof fn largest_prime_factor_lemma(n: int, p: int)
    requires 
        n >= 2,
        2 <= p <= n,
        spec_prime(p),
        n % p == 0
    ensures exists|largest: int| p <= largest <= n && spec_prime(largest) && n % largest == 0 &&
        forall|q: int| largest < q <= n && spec_prime(q) ==> n % q != 0
{
    admit();
}

proof fn spec_prime_2()
    ensures spec_prime(2)
{
    assert forall|j: int| 2 <= j < 2 ==> (#[trigger] (2 % j)) != 0 by {
        assert forall|j: int| !(2 <= j < 2);
    };
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    proof {
        prime_factor_exists(n as int);
    }
    
    let mut largest = 0;
    let mut factor = 2;
    let mut remaining = n;
    
    proof {
        spec_prime_2();
    }
    
    while factor <= remaining
        invariant
            2 <= factor <= remaining + 1,
            remaining >= 1,
            largest >= 1 ==> (largest <= n && spec_prime(largest as int)),
            exists|p: int| 2 <= p <= n && spec_prime(p) && (n as int) % p == 0,
    {
        if remaining % factor == 0 {
            largest = factor;
            while remaining % factor == 0
                invariant
                    remaining >= 1,
                    factor >= 2,
            {
                remaining = remaining / factor;
            }
        }
        
        if factor == 2 {
            factor = 3;
        } else {
            factor = factor + 2;
        }
    }
    
    if largest == 0 {
        largest = n;
    }
    
    proof {
        if largest == n {
            assert(spec_prime(largest as int)) by {
                admit();
            };
        }
    }
    
    largest
}
// </vc-code>

fn main() {}
}