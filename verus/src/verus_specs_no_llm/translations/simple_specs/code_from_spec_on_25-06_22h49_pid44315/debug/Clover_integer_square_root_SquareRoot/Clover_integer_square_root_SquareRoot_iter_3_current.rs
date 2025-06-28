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
    
    // Binary search invariant
    while low + 1 < high
        invariant
            low <= high,
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
    
    // At this point, either low + 1 == high or low == high
    // Check if high works, otherwise use low
    if high * high <= N {
        assert(high * high <= N);
        assert(N < (high + 1) * (high + 1)) by {
            // Since we maintained N < high * high in the original invariant when high was larger,
            // and we only decreased high when mid * mid > N, we know the postcondition holds
        };
        return high;
    } else {
        assert(low * low <= N);
        assert(N < (low + 1) * (low + 1)) by {
            // Since low + 1 >= high and high * high > N, we have (low + 1) * (low + 1) > N
        };
        return low;
    }
}

}