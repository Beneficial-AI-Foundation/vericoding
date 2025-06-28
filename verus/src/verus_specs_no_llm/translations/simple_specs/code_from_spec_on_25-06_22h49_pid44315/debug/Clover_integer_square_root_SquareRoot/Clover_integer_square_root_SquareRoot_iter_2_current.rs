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
    let mut high: nat = N;
    
    // Binary search invariant: low*low <= N < (high+1)*(high+1)
    while low < high
        invariant
            low <= high,
            low * low <= N,
            N < (high + 1) * (high + 1)
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        if mid * mid <= N {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    // At this point low == high, need to check which value satisfies the postcondition
    if low * low <= N {
        return low;
    } else {
        return low - 1;
    }
}

}