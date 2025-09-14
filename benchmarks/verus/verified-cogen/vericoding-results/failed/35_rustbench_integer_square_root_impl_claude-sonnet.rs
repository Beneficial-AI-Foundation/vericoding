// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type casting for safe_mul_bound and mul_bounds_lemma */
spec fn safe_mul_bound(x: i32) -> bool {
    x <= 46340 && x >= -46340
}

proof fn mul_bounds_lemma(x: i32, y: i32)
    requires safe_mul_bound(x), safe_mul_bound(y)
    ensures x * y >= -2147395600 && x * y <= 2147395600
{
    assert(x <= 46340 && x >= -46340);
    assert(y <= 46340 && y >= -46340);
    assert(46340 * 46340 == 2147395600);
}

proof fn sqrt_upper_bound_lemma(n: i32)
    requires n >= 1 && n <= 2147483647
    ensures n <= 46340
{
    if n > 46340 {
        assert(46340 * 46340 == 2147395600);
        assert(46341 * 46341 > 2147395600);
        assert(n >= 46341);
        assert(n * n >= 46341 * 46341);
        assert(false);
    }
}
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cast expressions to i32 to fix type mismatch errors */
    proof {
        sqrt_upper_bound_lemma(n);
    }
    
    let mut low = 0;
    let mut high = if n <= 46340 { n } else { 46340 };
    
    proof {
        assert(safe_mul_bound(high));
        assert(safe_mul_bound((high + 1) as i32));
        mul_bounds_lemma((high + 1) as i32, (high + 1) as i32);
        if n <= 46340 {
            assert(high == n);
            if n < 46340 {
                assert(n + 1 <= 46340);
                assert(safe_mul_bound((n + 1) as i32));
                mul_bounds_lemma((n + 1) as i32, (n + 1) as i32);
            }
        } else {
            assert(high == 46340);
            assert(46340 * 46340 == 2147395600);
            assert(46341 * 46341 > 2147395600);
            assert(n < 46341 * 46341);
        }
    }
    
    while low < high
        invariant
            0 <= low,
            low <= high,
            high <= 46340,
            safe_mul_bound(low),
            safe_mul_bound(high),
            low * low <= n,
            n < (high + 1) * (high + 1)
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        proof {
            assert(low <= mid && mid <= high);
            assert(safe_mul_bound(mid));
            assert(safe_mul_bound((mid + 1) as i32));
            mul_bounds_lemma(mid, mid);
            mul_bounds_lemma((mid + 1) as i32, (mid + 1) as i32);
        }
        
        let mid_squared = mid * mid;
        if mid_squared <= n {
            let next_squared = (mid + 1) * (mid + 1);
            if next_squared > n {
                proof {
                    assert(mid * mid <= n);
                    assert((mid + 1) * (mid + 1) > n);
                }
                return mid;
            }
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    proof {
        assert(low == high);
        assert(low * low <= n);
        assert(n < (low + 1) * (low + 1));
    }
    
    low
}
// </vc-code>

}
fn main() {}