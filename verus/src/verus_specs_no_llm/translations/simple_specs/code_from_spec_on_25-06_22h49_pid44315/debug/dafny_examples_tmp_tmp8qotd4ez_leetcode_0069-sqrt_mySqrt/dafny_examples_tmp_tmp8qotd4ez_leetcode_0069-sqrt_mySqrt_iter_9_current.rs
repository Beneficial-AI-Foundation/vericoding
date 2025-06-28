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
            0 <= high <= x,
            0 <= result <= high,
            result * result <= x,
            // All values from 0 to result have square <= x
            forall |i: int| 0 <= i <= result ==> i * i <= x,
            // All values > high have square > x (when high < x)
            forall |i: int| high < i <= x ==> i * i > x,
            // result is the largest value we found so far with square <= x
            forall |i: int| result < i <= high ==> i * i > x,
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
    // Case analysis based on the final state
    if result == high {
        // result is at the upper bound
        // From invariant: forall i: result < i <= high ==> i * i > x
        // Since result = high, this means forall i: high < i <= high is vacuously true
        // But we also have: forall i: high < i <= x ==> i * i > x
        // So result + 1 > high, therefore (result + 1) * (result + 1) > x
        assert(result + 1 > high);
        assert((result + 1) * (result + 1) > x);
    } else {
        // result < high
        // From invariant: forall i: result < i <= high ==> i * i > x
        // Since result < result + 1 <= high, we have (result + 1) * (result + 1) > x
        assert(result < high);
        assert(result + 1 <= high);
        assert((result + 1) * (result + 1) > x);
    }
    
    assert(sqrt(x, result));
    result
}

}