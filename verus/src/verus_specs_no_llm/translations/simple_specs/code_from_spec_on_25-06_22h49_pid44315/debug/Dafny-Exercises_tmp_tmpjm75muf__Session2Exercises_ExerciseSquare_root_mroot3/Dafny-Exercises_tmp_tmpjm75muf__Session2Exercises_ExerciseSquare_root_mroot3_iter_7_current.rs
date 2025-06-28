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
    
    // Binary search to find the largest integer r such that r*r*r <= n
    while low < high
        invariant
            0 <= low,
            low <= high,
            high <= n,
            // low*low*low <= n (the answer is at least low)
            low * low * low <= n,
            // (high+1)*(high+1)*(high+1) > n (the answer is at most high)
            (high + 1) * (high + 1) * (high + 1) > n,
        decreases high - low
    {
        let mid = low + (high - low + 1) / 2;
        
        proof {
            assert(low < high);
            assert((high - low + 1) >= 2);
            assert((high - low + 1) / 2 >= 1);
            assert(mid == low + (high - low + 1) / 2);
            assert(mid > low);
            assert(mid <= high);
        }
        
        if mid * mid * mid <= n {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    
    // At this point low == high, so low is the largest integer where low*low*low <= n
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