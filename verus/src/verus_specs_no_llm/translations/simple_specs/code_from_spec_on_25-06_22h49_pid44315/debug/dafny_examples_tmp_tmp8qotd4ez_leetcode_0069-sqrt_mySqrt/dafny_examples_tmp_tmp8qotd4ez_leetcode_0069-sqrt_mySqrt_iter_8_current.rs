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
            0 <= low <= high + 1,
            high <= x,
            0 <= result,
            result * result <= x,
            // If result was updated, then low = result + 1
            low > 0 ==> result >= low - 1,
            // All values < low either have square > x or are <= result
            forall |i: int| 0 <= i < low ==> (i * i > x || i <= result),
            // All values > high have square > x  
            forall |i: int| high < i <= x ==> i * i > x,
            // result is a valid candidate
            forall |i: int| result < i < low ==> i * i > x,
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        assert(low <= mid <= high);
        
        let mid_squared = mid * mid;
        
        if mid_squared <= x {
            result = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    // When we exit the loop: low > high
    assert(low > high);
    
    // From invariants we know result * result <= x
    assert(result * result <= x);
    
    // Need to prove (result + 1) * (result + 1) > x
    // We know low > high, so low >= high + 1
    // From invariant: all i > high have i * i > x
    // Since low > high and low = result + 1 (from algorithm), 
    // we have (result + 1) * (result + 1) > x
    
    // The key insight: when low > high, either:
    // 1. We never updated result, so result = 0 and we need to check if 1*1 > x
    // 2. We updated result in the last valid iteration
    
    if result == 0 {
        // If result is still 0, then 1*1 must be > x
        assert(1 > x || x == 1) by {
            // From invariant: forall i < low, either i*i > x or i <= result=0
            // Since low > high >= 0, we have low >= 1
            // So 1 < low, which means either 1*1 > x or 1 <= 0
            // Since 1 > 0, we must have 1*1 > x, so x < 1
            // But x >= 0 and x != 0,1 (handled above), contradiction
        };
        assert((result + 1) * (result + 1) > x);
    } else {
        // result > 0, so we updated result at some point
        // From the invariant forall i: result < i < low ==> i * i > x
        // We know result < result + 1
        // If result + 1 < low, then (result + 1) * (result + 1) > x
        // If result + 1 >= low, then since low > high, result + 1 > high
        // From invariant: forall i > high, i * i > x
        assert((result + 1) * (result + 1) > x) by {
            if result + 1 < low {
                // From invariant: forall i: result < i < low ==> i * i > x
                assert((result + 1) * (result + 1) > x);
            } else {
                // result + 1 >= low > high
                // From invariant: forall i > high, i * i > x
                assert(result + 1 > high);
                assert((result + 1) * (result + 1) > x);
            }
        };
    }
    
    assert(sqrt(x, result));
    result
}

}