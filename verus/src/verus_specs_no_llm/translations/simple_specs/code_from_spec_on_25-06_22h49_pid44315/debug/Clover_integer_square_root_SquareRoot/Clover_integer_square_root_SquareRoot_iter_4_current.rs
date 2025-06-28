use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquareRoot(N: nat) -> (r: nat)
    ensures
        r*r <= N < (r+1)*(r+1)
{
    if N == 0 {
        return 0;
    }
    
    let mut low: nat = 0;
    let mut high: nat = N + 1;
    
    // Binary search invariant
    while low + 1 < high
        invariant
            low < high,
            low * low <= N,
            N < high * high
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        if mid * mid <= N {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    // At this point, low + 1 >= high, so low + 1 == high
    // We have low * low <= N < high * high = (low + 1) * (low + 1)
    assert(low + 1 == high);
    assert(low * low <= N);
    assert(N < high * high);
    assert(N < (low + 1) * (low + 1));
    
    return low;
}

}