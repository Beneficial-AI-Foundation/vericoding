use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mroot3(n: int) -> (r: int) //Cost O(log n)
    requires
        n>=0
    ensures
        r>=0 && r*r*r <= n < (r+1)*(r+1)*(r+1)
{
    if n == 0 {
        return 0;
    }
    
    if n == 1 {
        return 1;
    }
    
    let mut low: int = 0;
    let mut high: int = n;
    
    // Find a better upper bound where (high+1)^3 > n
    while (high + 1) * (high + 1) * (high + 1) <= n
        invariant
            0 <= low,
            low <= high,
            low * low * low <= n,
        decreases n - high
    {
        high = high + 1;
    }
    
    // Now we have (high+1)^3 > n, so we can do binary search
    while low < high
        invariant
            0 <= low,
            low <= high,
            low * low * low <= n,
            (high + 1) * (high + 1) * (high + 1) > n,
        decreases high - low
    {
        let mid = (low + high + 1) / 2;
        
        proof {
            assert(low < high);
            assert(low + 1 <= high + 1);
            assert((low + high + 1) / 2 >= (low + low + 1) / 2);
            assert((low + high + 1) / 2 >= low + 1);
            assert(mid > low);
            assert((low + high + 1) / 2 <= (high + high + 1) / 2);
            assert(mid <= high);
        }
        
        if mid * mid * mid <= n {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    
    // At this point low == high, so low is the cube root
    proof {
        assert(low == high);
        assert(low >= 0);
        assert(low * low * low <= n);
        assert((low + 1) * (low + 1) * (low + 1) > n);
        assert(n < (low + 1) * (low + 1) * (low + 1));
    }
    
    low
}

}