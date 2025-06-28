use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mroot3(n: int) -> (r: int) //Cost O(log n)
    requires
        n>=0
    ensures
        r>=0 && r*r <= n < (r+1)*(r+1)
{
    if n == 0 {
        return 0;
    }
    
    if n == 1 {
        return 1;
    }
    
    let mut low: int = 0;
    let mut high: int = n;
    
    // Binary search invariant: low*low <= n < (high+1)*(high+1)
    while low < high
        invariant
            0 <= low <= high <= n,
            low * low <= n,
            n < (high + 1) * (high + 1),
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        
        if mid * mid <= n {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    // At this point low > high, so we need to return high
    // because high is the largest integer where high*high <= n
    assert(low > high);
    assert(high * high <= n);
    assert(n < (high + 1) * (high + 1));
    
    high
}

}