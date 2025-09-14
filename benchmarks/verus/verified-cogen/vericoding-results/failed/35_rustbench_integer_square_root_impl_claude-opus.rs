// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow by adding explicit bounds checks */
    let mut low: i32 = 0;
    let mut high: i32 = if n > 46340 { 46340 } else { n };
    let mut result: i32 = 0;
    
    while low <= high
        invariant
            0 <= low,
            0 <= high,
            high <= 46340,
            0 <= result,
            result <= 46340,
            result * result <= n,
            low > 0 ==> (low - 1) <= 46340,
            low > 0 ==> (low - 1) * (low - 1) <= n,
            result < low ==> result * result <= n,
            high < n ==> high < 46340,
            high < n ==> n < (high + 1) * (high + 1),
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        assert(0 <= mid);
        assert(mid <= high);
        assert(mid <= 46340);
        
        if mid <= 46340 && mid * mid <= n {
            result = mid;
            if mid * mid == n {
                proof {
                    assert(result * result == n);
                    assert(result * result <= n);
                    assert(result < 46340 || result == 46340);
                    if result < 46340 {
                        assert((result + 1) * (result + 1) == result * result + 2 * result + 1);
                        assert((result + 1) * (result + 1) > result * result);
                        assert((result + 1) * (result + 1) > n);
                    }
                }
                return result;
            }
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    proof {
        assert(low > high);
        assert(result * result <= n);
        assert(result <= 46340);
        
        if result < 46340 {
            assert(high == result);
            assert(low == result + 1);
            assert(low <= 46340);
            
            if low * low > n {
                assert((result + 1) * (result + 1) > n);
            } else {
                assert(low * low <= n);
                assert(result < low);
                assert(result * result <= n);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}