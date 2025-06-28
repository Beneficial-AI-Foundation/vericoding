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
            0 <= low,
            high <= x,
            0 <= result,
            result * result <= x,
            // If we found a result, then result < low (all values < low have been processed)
            result < low,
            // All values > high have square > x
            forall |i: int| high < i <= x ==> i * i > x,
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
    // 2. result < low
    // 3. low > high, so result <= high
    // 4. forall i: high < i <= x ==> i * i > x
    
    assert(result * result <= x);
    
    // Since low > high and result < low, we have result <= high
    // So result + 1 > high (since result + 1 >= low > high)
    // From the invariant: forall i: high < i <= x ==> i * i > x  
    // Since result + 1 > high and result + 1 <= x (we need to prove this)
    
    // We know result < low and low > high, so result <= high
    // Also result >= 0 and result * result <= x
    // If result + 1 <= x, then from invariant (result + 1) * (result + 1) > x
    // If result + 1 > x, then clearly (result + 1) * (result + 1) > x
    
    if result + 1 <= x {
        // Use the invariant: forall i: high < i <= x ==> i * i > x
        // Since result < low and low > high, we have result <= high
        // So result + 1 > high (because result + 1 >= low > high)
        assert(result + 1 > high);
        assert((result + 1) * (result + 1) > x);
    } else {
        // result + 1 > x >= (result + 1), so (result + 1) * (result + 1) > x
        assert((result + 1) * (result + 1) > x);
    }
    
    assert(sqrt(x, result));
    result
}

}