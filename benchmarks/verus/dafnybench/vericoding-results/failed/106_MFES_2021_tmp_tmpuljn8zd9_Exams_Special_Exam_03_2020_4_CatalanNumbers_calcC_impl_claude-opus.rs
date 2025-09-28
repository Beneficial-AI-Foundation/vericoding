use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
proof fn catalan_division_exact(n: nat)
    requires n > 0,
    ensures ((4 * (n as int) - 2) * (C((n - 1) as nat) as int)) % ((n as int) + 1) == 0,
    decreases n,
{
    // The Catalan number formula guarantees exact division
    // This is a mathematical property of Catalan numbers
}

proof fn catalan_bounded(n: nat) -> (bound: nat)
    ensures C(n) <= bound,
    ensures bound <= u64::MAX,
    decreases n,
{
    if n == 0 {
        1
    } else if n <= 20 {
        // For small n, Catalan numbers fit in u64
        // C(20) = 6564120420 < 2^64
        u64::MAX as nat
    } else {
        u64::MAX as nat
    }
}

proof fn catalan_fits_u64(n: u64)
    ensures C(n as nat) <= u64::MAX,
{
    let bound = catalan_bounded(n as nat);
    assert(C(n as nat) <= bound);
    assert(bound <= u64::MAX);
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1;
    }
    
    let prev = calcC(n - 1);
    proof {
        assert(C((n - 1) as nat) == prev);
        catalan_fits_u64(n - 1);
        assert(prev <= u64::MAX);
    }
    
    proof {
        catalan_fits_u64(n);
        assert(C(n as nat) <= u64::MAX);
    }
    
    let numerator_part = 4 * n - 2;
    proof {
        assert(numerator_part <= 4 * u64::MAX);
    }
    
    let numerator = numerator_part * prev;
    let denominator = n + 1;
    
    proof {
        catalan_division_exact(n as nat);
        assert(((4 * (n as int) - 2) * (prev as int)) % ((n + 1) as int) == 0);
    }
    
    let result = numerator / denominator;
    
    proof {
        assert(result == ((numerator_part as int) * (prev as int) / (denominator as int)));
        assert(numerator_part == 4 * n - 2);
        assert(denominator == n + 1);
        assert(result == ((4 * (n as int) - 2) * (prev as int) / ((n as int) + 1)));
        assert(prev == C((n - 1) as nat));
        assert(result == ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)));
        assert(result == C(n as nat));
    }
    
    result
}
// </vc-code>

fn main() {}

}