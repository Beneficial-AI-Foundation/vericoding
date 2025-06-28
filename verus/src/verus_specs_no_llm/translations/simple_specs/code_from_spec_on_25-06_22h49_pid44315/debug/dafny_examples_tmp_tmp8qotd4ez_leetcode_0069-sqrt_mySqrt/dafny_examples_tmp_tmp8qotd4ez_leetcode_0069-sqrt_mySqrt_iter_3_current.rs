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
            0 <= result <= high,
            result * result <= x,
            (high + 1) * (high + 1) > x,
            low <= result + 1,
            forall |r: int| low <= r <= high ==> (r * r <= x ==> (r + 1) * (r + 1) > x || r <= result),
    {
        let mid = (low + high) / 2;
        let mid_squared = mid * mid;
        
        assert(low <= mid <= high);
        
        if mid_squared == x {
            assert(mid * mid <= x);
            assert((mid + 1) * (mid + 1) > x) by {
                assert((mid + 1) * (mid + 1) == mid * mid + 2 * mid + 1);
                assert(2 * mid + 1 > 0);
                assert(mid * mid + 2 * mid + 1 > mid * mid);
            };
            return mid;
        } else if mid_squared < x {
            result = mid;
            low = mid + 1;
            assert(result <= high);
        } else {
            high = mid - 1;
            assert(result <= high);
        }
    }
    
    // When we exit the loop, low > high
    assert(low > high);
    assert(low >= high + 1);
    assert(result <= high);
    assert(low >= result + 1);
    
    // From invariant: (high + 1) * (high + 1) > x
    // Since result <= high, we have result + 1 <= high + 1
    assert(result + 1 <= high + 1);
    assert((result + 1) * (result + 1) <= (high + 1) * (high + 1));
    assert((result + 1) * (result + 1) > x) by {
        assert((high + 1) * (high + 1) > x);
        if (result + 1) * (result + 1) <= x {
            assert((result + 1) * (result + 1) <= x < (high + 1) * (high + 1));
            assert(result + 1 < high + 1);
            assert(result < high);
            assert(result + 1 <= high);
            assert(low <= result + 1 <= high);
            // This contradicts low > high
            assert(false);
        }
    };
    
    result
}

}

The key changes I made:


The proof now correctly establishes that when the loop terminates, `result` satisfies the square root property: `result * result <= x` and `(result + 1) * (result + 1) > x`.