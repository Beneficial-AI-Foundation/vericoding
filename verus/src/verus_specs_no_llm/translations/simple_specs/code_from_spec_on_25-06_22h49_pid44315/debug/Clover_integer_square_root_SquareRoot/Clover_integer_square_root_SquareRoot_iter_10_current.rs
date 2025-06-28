use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sqrt_upper_bound(n: nat) -> nat {
    n + 1
}

proof fn lemma_sqrt_upper_bound(n: nat)
    ensures n < sqrt_upper_bound(n) * sqrt_upper_bound(n)
{
    let upper = n + 1;
    assert(upper * upper == (n + 1) * (n + 1));
    assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
    
    if n == 0 {
        assert(1 > 0);
    } else {
        // For n >= 1, we have n^2 >= n and 2n >= 2 >= 1
        assert(n * n >= n) by {
            assert(n >= 1);
            assert(n * n >= n * 1);
        };
        assert(2 * n >= 2) by {
            assert(n >= 1);
            assert(2 * n >= 2 * 1);
        };
        assert(n * n + 2 * n + 1 >= n + 2 + 1);
        assert(n + 3 > n);
    }
}

proof fn lemma_mid_bounds(low: nat, high: nat, mid: nat)
    requires 
        low + 1 < high,
        mid == (low + high) / 2
    ensures 
        low < mid < high
{
    // In integer division, (low + high) / 2 >= low and < high when low + 1 < high
    assert(low + high >= 2 * low + 1) by {
        assert(high >= low + 1);
        assert(low + high >= low + low + 1);
        assert(low + low + 1 == 2 * low + 1);
    };
    assert((low + high) / 2 >= low);
    
    assert(low + high < 2 * high) by {
        assert(low < high);
        assert(low + high < high + high);
        assert(high + high == 2 * high);
    };
    assert((low + high) / 2 < high);
    
    // Since we know low + 1 < high, mid cannot equal low
    if mid == low {
        assert((low + high) / 2 == low);
        assert(low + high < 2 * low + 2) by {
            assert(high < low + 2);
            assert(low + high < low + low + 2);
        };
        assert(2 * low <= low + high < 2 * low + 2);
        assert((low + high) / 2 == low);
        assert(false); // This is a contradiction since we showed mid > low above
    }
    assert(mid > low);
}

fn SquareRoot(N: nat) -> (r: nat)
    ensures
        r*r <= N < (r+1)*(r+1)
{
    if N == 0 {
        return 0;
    }
    
    let mut low: nat = 0;
    let mut high: nat = sqrt_upper_bound(N);
    
    // Establish initial bounds
    proof {
        lemma_sqrt_upper_bound(N);
    }
    
    // Binary search
    while low + 1 < high
        invariant
            low < high,
            low * low <= N,
            N < high * high
        decreases high - low
    {
        let mid: nat = (low + high) / 2;
        
        proof {
            lemma_mid_bounds(low, high, mid);
        }
        
        if mid * mid <= N {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    // Post-loop reasoning
    assert(low + 1 >= high);
    assert(low < high);
    assert(low + 1 == high);
    assert(low * low <= N);
    assert(N < high * high);
    assert(high == low + 1);
    assert(N < (low + 1) * (low + 1));
    
    low
}

}