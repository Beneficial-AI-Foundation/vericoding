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
    
    if x == 1 {
        return 1;
    }
    
    let mut low: int = 0;
    let mut high: int = x;
    let mut result: int = 0;
    
    while low <= high
        invariant
            0 <= low <= high + 1 <= x + 1,
            0 <= result,
            result * result <= x,
            // If low > 0, then (low-1)^2 <= x
            low > 0 ==> (low - 1) * (low - 1) <= x,
            // If high < x, then (high+1)^2 > x  
            high < x ==> (high + 1) * (high + 1) > x,
            // result is the largest seen value whose square <= x
            forall |i: int| 0 <= i < low ==> i * i <= x || i > result,
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        // Mid is between low and high
        assert(low <= mid <= high);
        
        let mid_squared = mid * mid;
        
        if mid_squared <= x {
            result = mid;
            low = mid + 1;
            
            // Prove that result^2 <= x
            assert(result * result <= x);
        } else {
            // mid_squared > x, so we search in lower half
            high = mid - 1;
            
            // Prove that (high+1)^2 > x when high < x
            assert(mid_squared > x);
            assert(high == mid - 1);
            assert((high + 1) * (high + 1) == mid_squared);
            assert(high + 1 == mid);
        }
    }
    
    // When we exit the loop: low > high
    // result is the largest integer whose square <= x
    assert(low > high);
    
    // We need to prove sqrt(x, result)
    // 1. result * result <= x (maintained by invariant)
    assert(result * result <= x);
    
    // 2. (result + 1) * (result + 1) > x
    // Since low > high and low = result + 1 or greater
    assert(low >= result + 1) by {
        // In each iteration where we set result = mid, we also set low = mid + 1
        // So low is always result + 1 when we update result
    };
    
    if low == result + 1 {
        // We need to show that low * low > x
        // Since we exited the loop, we never found a value >= low with square <= x
        assert((result + 1) * (result + 1) > x) by {
            // If (result + 1)^2 <= x, then we would have continued the loop
            // and updated result to result + 1, but we didn't
            if (result + 1) * (result + 1) <= x {
                // This contradicts our loop termination
                assert(low <= high); // This would be true, contradicting low > high
                assert(false);
            }
        };
    } else {
        // low > result + 1, so (result + 1)^2 < low^2
        // and we know low^2 > x from our search
        assert(low > result + 1);
        assert((result + 1) * (result + 1) < low * low);
        assert((result + 1) * (result + 1) > x) by {
            if (result + 1) * (result + 1) <= x {
                // Then result + 1 should have been a valid candidate
                // But our binary search would have found it
                assert(result + 1 < low);
                assert((result + 1) * (result + 1) <= x);
                // This means there's a gap in our search, which shouldn't happen
                // in a proper binary search
                assert(false);
            }
        };
    }
    
    assert(sqrt(x, result));
    result
}

}