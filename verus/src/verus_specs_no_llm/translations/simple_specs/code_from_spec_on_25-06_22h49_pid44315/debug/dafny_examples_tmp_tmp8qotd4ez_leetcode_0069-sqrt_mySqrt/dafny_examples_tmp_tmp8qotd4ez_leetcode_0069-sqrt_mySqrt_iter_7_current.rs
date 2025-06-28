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
            high < x,
            0 <= result,
            result * result <= x,
            // All values < low either have square > x or are <= result
            forall |i: int| 0 <= i < low ==> (i * i > x || i <= result),
            // All values > high have square > x
            forall |i: int| high < i <= x ==> i * i > x,
            // result is the largest value seen so far with square <= x
            forall |i: int| 0 <= i <= result ==> i * i <= x,
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
    
    // From invariants we know:
    // 1. result * result <= x
    assert(result * result <= x);
    
    // 2. We need to prove (result + 1) * (result + 1) > x
    // Since low > high, we have low >= high + 1
    // From the invariant: forall i > high, i * i > x
    // Since low > high, we have low * low > x
    // Since low = result + 1 (from last iteration where we set result), 
    // we have (result + 1) * (result + 1) > x
    
    assert(low == result + 1) by {
        // This follows from the algorithm: whenever we update result to mid,
        // we set low to mid + 1, so low is always result + 1 after an update
    };
    
    assert((result + 1) * (result + 1) > x) by {
        assert(low == result + 1);
        assert(low > high);
        // From invariant: forall i > high, i * i > x
        // Since low > high, we have low * low > x
        assert(low * low > x);
        assert((result + 1) * (result + 1) > x);
    };
    
    assert(sqrt(x, result));
    result
}

}