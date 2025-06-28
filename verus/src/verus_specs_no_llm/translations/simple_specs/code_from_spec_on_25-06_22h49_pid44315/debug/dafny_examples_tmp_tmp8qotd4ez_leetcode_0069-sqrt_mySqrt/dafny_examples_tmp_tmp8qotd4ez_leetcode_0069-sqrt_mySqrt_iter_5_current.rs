use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sqrt(x: int, r: int) -> bool {
    r*r <= x && (r+1)*(r+1) > x
}

fn mySqrt(x: int) -> (res: int)
    requires
        0 <= x
    ensures
        sqrt(x, res)
{
    if x == 0 {
        return 0;
    }
    
    let mut low: int = 0;
    let mut high: int = x;
    let mut result: int = 0;
    
    while low <= high
        invariant
            0 <= low <= high + 1,
            0 <= result <= high + 1,
            result * result <= x,
            low > 0 ==> (low - 1) * (low - 1) <= x,
            high < x ==> (high + 1) * (high + 1) > x,
    {
        let mid = (low + high) / 2;
        
        assert(low <= mid <= high);
        
        let mid_squared = mid * mid;
        
        if mid_squared == x {
            assert(sqrt(x, mid)) by {
                assert(mid * mid <= x);
                assert((mid + 1) * (mid + 1) == mid * mid + 2 * mid + 1);
                assert(mid >= 0);
                assert(2 * mid + 1 >= 1);
                assert((mid + 1) * (mid + 1) > x);
            };
            return mid;
        } else if mid_squared < x {
            result = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    // When we exit the loop, low > high
    assert(low > high);
    assert(result <= high);
    assert(result * result <= x);
    
    // Prove that (result + 1) * (result + 1) > x
    assert((result + 1) * (result + 1) > x) by {
        assert(low == high + 1);
        assert(result <= high);
        assert(result + 1 <= high + 1);
        assert(result + 1 <= low);
        
        // Since low > high and we've been doing binary search,
        // low represents the smallest value whose square is > x
        assert(low * low > x) by {
            // If low * low <= x, then we should have continued the loop
            // with low in our search range, but we exited because low > high
            if low * low <= x {
                // This would mean we should have set high >= low in some iteration
                // But we exited with low > high, contradiction
                assert(false);
            }
        };
        
        assert(result + 1 <= low);
        if result + 1 == low {
            assert((result + 1) * (result + 1) == low * low);
            assert((result + 1) * (result + 1) > x);
        } else {
            assert(result + 1 < low);
            assert((result + 1) * (result + 1) <= result * result + 2 * result + 1);
            // We need to show that even result + 1 < low implies (result + 1)^2 > x
            // Since low is the first integer where low^2 > x, and result + 1 < low,
            // we need a different approach
            
            // Actually, let's use the fact that in binary search,
            // if we exit with low > high, then high is the largest value
            // such that high^2 <= x, so high + 1 is the first value > x
            assert(high * high <= x || high < 0);
            assert((high + 1) * (high + 1) > x);
            assert(result <= high);
            if result == high {
                assert((result + 1) * (result + 1) == (high + 1) * (high + 1));
                assert((result + 1) * (result + 1) > x);
            } else {
                assert(result < high);
                assert(result + 1 <= high);
                if result + 1 == high {
                    // Then (result + 1)^2 = high^2 <= x, but (high + 1)^2 > x
                    // We need high^2 < x for this case
                    if (result + 1) * (result + 1) <= x {
                        assert(high * high <= x);
                        assert(high * high < x || high * high == x);
                        if high * high == x {
                            assert((high + 1) * (high + 1) > x);
                            assert(result + 1 == high);
                            assert((result + 1) * (result + 1) == x);
                            assert(false); // contradiction since (result + 1)^2 <= x but == x and > x
                        }
                    }
                } else {
                    assert(result + 1 < high);
                    // This case is tricky, let's reconsider our approach
                    assert((result + 1) * (result + 1) <= high * high);
                    if (result + 1) * (result + 1) <= x {
                        // Then result + 1 should have been our result, not result
                        assert(false);
                    }
                }
            }
        }
    };
    
    result
}

}