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
    
    // Binary search to find the largest integer r such that r*r <= n
    while low <= high
        invariant
            0 <= low,
            high <= n,
            // The answer r satisfies: low-1 < r <= high
            // Meaning: if low > 0, then (low-1)*(low-1) <= n
            // and (high+1)*(high+1) > n
            (low == 0 || (low - 1) * (low - 1) <= n),
            (high == n || (high + 1) * (high + 1) > n),
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        
        if mid * mid <= n {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    // At this point low > high, so high is the largest integer where high*high <= n
    assert(low > high);
    
    // We need to prove that high satisfies our postcondition
    assert(high >= 0); // follows from invariant and the fact that we handled n=0,1 cases
    assert(high * high <= n); // follows from invariant
    assert(n < (high + 1) * (high + 1)); // follows from invariant
    
    high
}

}