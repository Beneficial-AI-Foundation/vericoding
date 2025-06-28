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
    
    let mut low: int = 0;
    let mut high: int = n;
    
    // Binary search invariant: low*low <= n < (high+1)*(high+1)
    while low < high
        invariant
            0 <= low <= high,
            low * low <= n,
            n < (high + 1) * (high + 1)
    {
        let mid = low + (high - low + 1) / 2;
        
        if mid * mid <= n {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    
    low
}

}