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
    
    let mut low: usize = 0;
    let mut high: usize = (N + 1) as usize;
    
    // Binary search invariant
    while low + 1 < high
        invariant
            low < high,
            (low as nat) * (low as nat) <= N,
            N < (high as nat) * (high as nat),
            high <= N + 1,
            high >= 1
        decreases high - low
    {
        // Use integer division that's well-defined for usize  
        let mid: usize = low + (high - low) / 2;
        
        assert(low < mid < high);
        
        if (mid as nat) * (mid as nat) <= N {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    // At this point, low + 1 >= high
    // Since low < high from invariant and low + 1 >= high, we have low + 1 == high
    // We have low * low <= N < high * high = (low + 1) * (low + 1)
    assert(low + 1 >= high);
    assert(low < high);
    assert(low + 1 == high);
    assert((low as nat) * (low as nat) <= N);
    assert(N < (high as nat) * (high as nat));
    assert(high as nat == (low as nat) + 1);
    assert(N < ((low as nat) + 1) * ((low as nat) + 1));
    
    low as nat
}

}