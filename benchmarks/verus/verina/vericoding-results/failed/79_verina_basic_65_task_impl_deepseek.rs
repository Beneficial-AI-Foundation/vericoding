// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix strict multiplication monotonicity lemma and square proofs */
proof fn lemma_multiply_monotonicity(x: int, y: int, z: int)
    requires
        x <= y,
        z >= 0,
    ensures
        x * z <= y * z,
{
    if z > 0 {
        assert((y - x) * z >= 0) by {
            assert(y - x >= 0);
        };
        assert(x * z + (y - x) * z == y * z);
    } else {
        assert(z == 0);
        assert(x * z == 0 && y * z == 0);
    }
}

proof fn lemma_square_identity(x: int) 
    ensures
        x * x >= 0,
{
    if x >= 0 {
        assert(x * x >= 0);
    } else {
        let neg_x = -x;
        assert(neg_x > 0);
        assert(x * x == neg_x * neg_x);
        assert(neg_x * neg_x >= 0);
    }
}

proof fn lemma_square_monotonicity(x: int, y: int)
    requires
        0 <= x <= y,
    ensures
        x * x <= y * y,
{
    lemma_multiply_monotonicity(x, y, x);
    lemma_multiply_monotonicity(x, y, y);
    assert(x * x == x * x);
    assert(y * y == y * y);
    assert(x * x <= x * y);
    assert(x * y <= y * y);
}

proof fn lemma_square_strict_monotonicity(x: int, y: int)
    requires
        0 <= x < y,
    ensures
        x * x < y * y,
{
    if x > 0 {
        lemma_multiply_monotonicity(x, y, x);
        lemma_multiply_monotonicity(x, y, y);
        assert(x * x < x * y) by {
            lemma_strict_multiply_monotonicity(x, y, x);
        };
        assert(x * y <= y * y);
    } else {
        assert(x == 0);
        assert(x * x == 0);
        assert(y > 0);
        assert(y * y > 0);
    }
}

proof fn lemma_strict_multiply_monotonicity(x: int, y: int, z: int)
    requires
        x < y,
        z > 0,
    ensures
        x * z < y * z,
{
    let diff = y - x;
    assert(diff > 0);
    assert(diff * z > 0);
    assert(x * z + diff * z == y * z);
}

spec fn is_square_root(r: int, n: int) -> bool
{
    r * r <= n && n < (r + 1) * (r + 1)
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix binary search implementation with proper overflow checks and verification */
    if n == 0 {
        return 0;
    }
    
    let mut low: usize = 0;
    let mut high: usize = n;
    
    proof {
        assert(high > 0);
        lemma_square_identity(high as int);
    }
    
    while low < high
        invariant
            low <= high <= n,
            low * low <= n,
            n < (high + 1) * (high + 1),
            decreases high - low,
    {
        let mid = low + (high - low) / 2;
        
        proof {
            assert(mid >= low && mid <= high);
        }
        
        let mid_sq = match mid.checked_mul(mid) {
            Some(sq) => sq,
            None => {
                high = mid;
                continue;
            }
        };
        
        if mid_sq <= n {
            proof {
                lemma_square_monotonicity(low as int, mid as int);
            }
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    let result = if low > 0 { low - 1 } else { 0 };
    
    proof {
        assert(result * result <= n) by {
            lemma_square_monotonicity(0, result as int);
        };
        
        assert(n < (result + 1) * (result + 1)) by {
            lemma_square_strict_monotonicity(result as int, (result + 1) as int);
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}