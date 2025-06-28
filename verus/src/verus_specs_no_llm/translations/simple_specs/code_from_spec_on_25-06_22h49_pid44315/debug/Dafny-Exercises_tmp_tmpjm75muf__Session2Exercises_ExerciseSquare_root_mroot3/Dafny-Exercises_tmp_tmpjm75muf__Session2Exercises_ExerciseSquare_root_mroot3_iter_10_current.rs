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
    let mut high: int = 1;
    
    // Find an upper bound where high^3 > n
    while high * high * high <= n
        invariant
            0 <= low,
            low <= high,
            low * low * low <= n,
            high >= 1,
        decreases n - high * high * high
    {
        low = high;
        high = high * 2;
    }
    
    // Now we have high^3 > n and low^3 <= n
    // Binary search to find the largest integer r such that r^3 <= n
    while low + 1 < high
        invariant
            0 <= low < high,
            low * low * low <= n,
            high * high * high > n,
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        proof {
            assert(low < mid < high);
        }
        
        if mid * mid * mid <= n {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    // At this point low + 1 >= high, so low + 1 == high
    // We know low^3 <= n and high^3 > n, so low is our answer
    proof {
        assert(low >= 0);
        assert(low * low * low <= n);
        assert((low + 1) * (low + 1) * (low + 1) > n);
    }
    
    low
}

}