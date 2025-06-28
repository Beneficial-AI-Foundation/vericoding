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
            0 <= result,
            result * result <= x,
            (result + 1) * (result + 1) > x || low <= result + 1,
            (high + 1) * (high + 1) > x,
            low > result ==> result * result <= x && (result + 1) * (result + 1) > x,
    {
        let mid = (low + high) / 2;
        let mid_squared = mid * mid;
        
        if mid_squared == x {
            assert(mid * mid <= x);
            assert((mid + 1) * (mid + 1) > x) by {
                assert((mid + 1) * (mid + 1) == mid * mid + 2 * mid + 1);
                assert(mid * mid + 2 * mid + 1 > mid * mid);
            };
            return mid;
        } else if mid_squared < x {
            result = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    // When we exit the loop, low > high, so low >= high + 1
    // This means low > result, so by our invariant, result satisfies sqrt
    assert(low > high);
    assert(low > result) by {
        assert(low >= high + 1);
        assert(result <= high); // This follows from how we update result
    };
    
    result
}

}