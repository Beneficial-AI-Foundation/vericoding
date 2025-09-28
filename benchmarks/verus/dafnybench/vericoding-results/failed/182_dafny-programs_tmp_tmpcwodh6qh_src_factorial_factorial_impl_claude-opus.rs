use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
// Helper lemma to prove factorial property
proof fn fact_unfold(n: nat)
    ensures 
        n == 0 ==> fact(n) == 1,
        n > 0 ==> fact(n) == n * fact((n - 1) as nat)
{
    reveal(fact);
}

// Helper to establish bounds on factorial values
proof fn fact_bound(n: nat)
    ensures
        n <= 12 ==> fact(n) <= 479001600
    decreases n
{
    reveal(fact);
    if n == 0 {
        assert(fact(0) == 1);
    } else if n <= 12 {
        fact_bound((n - 1) as nat);
        assert(fact((n - 1) as nat) <= 479001600);
        // Manual calculation shows fact(12) = 479001600
        if n == 1 { assert(fact(1) == 1); }
        else if n == 2 { assert(fact(2) == 2); }
        else if n == 3 { assert(fact(3) == 6); }
        else if n == 4 { assert(fact(4) == 24); }
        else if n == 5 { assert(fact(5) == 120); }
        else if n == 6 { assert(fact(6) == 720); }
        else if n == 7 { assert(fact(7) == 5040); }
        else if n == 8 { assert(fact(8) == 40320); }
        else if n == 9 { assert(fact(9) == 362880); }
        else if n == 10 { assert(fact(10) == 3628800); }
        else if n == 11 { assert(fact(11) == 39916800); }
        else if n == 12 { assert(fact(12) == 479001600); }
    }
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12  // to prevent overflow
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result: u32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            result == fact(i as nat),
            n <= 12,
        decreases n - i
    {
        i = i + 1;
        
        // Establish properties before multiplication
        proof {
            assert(i <= n);
            assert(n <= 12);
            assert(i <= 12);
            assert(result == fact((i - 1) as nat));
            
            // Prove no overflow
            fact_bound((i - 1) as nat);
            assert(fact((i - 1) as nat) <= 479001600);
            assert(result <= 479001600);
            assert((i as u32) <= 12);
            assert((result as u64) * (i as u64) <= 479001600u64 * 12u64);
            assert(479001600u64 * 12u64 < 4294967296u64); // 2^32
            assert((result as u64) * (i as u64) < 4294967296u64);
        }
        
        result = result * i;
        
        // Prove the invariant is maintained
        proof {
            assert(result == fact((i - 1) as nat) as u32 * i);
            fact_unfold(i as nat);
            assert(fact(i as nat) == (i as nat) * fact((i - 1) as nat));
            assert(result as nat == (i as nat) * fact((i - 1) as nat));
            assert(result == fact(i as nat));
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}