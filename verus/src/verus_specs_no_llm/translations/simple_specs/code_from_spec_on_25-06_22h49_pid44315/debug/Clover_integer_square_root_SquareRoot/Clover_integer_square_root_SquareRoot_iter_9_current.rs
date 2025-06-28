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
    
    // Establish initial bounds
    assert(low * low == 0);
    assert(low * low <= N);
    assert((N + 1) * (N + 1) == N * N + 2 * N + 1);
    assert(N < N * N + 2 * N + 1) by {
        if N >= 1 {
            assert(N * N >= N) by {
                assert(N * N >= N * 1);
                assert(N * 1 == N);
            };
            assert(2 * N >= N) by {
                assert(2 * N >= 1 * N);
                assert(1 * N == N);
            };
            assert(N * N + 2 * N >= N + N);
            assert(N * N + 2 * N + 1 >= N + N + 1);
            assert(N + N >= N);
            assert(N + N + 1 > N);
            assert(N * N + 2 * N + 1 > N);
        }
    };
    assert(N < high * high);
    
    // Binary search invariant
    while low + 1 < high
        invariant
            low < high,
            low * low <= N,
            N < high * high,
            high <= N + 1
        decreases high - low
    {
        let mid: nat = (low + high) / 2;
        
        assert(low < mid < high) by {
            assert(low + 1 < high);
            assert(low < (low + high) / 2);
            assert((low + high) / 2 < high);
        };
        
        if mid * mid <= N {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    // At this point, low + 1 >= high
    // Since low < high from invariant and low + 1 >= high, we have low + 1 == high
    assert(low + 1 >= high);
    assert(low < high);
    assert(low + 1 == high);
    assert(low * low <= N);
    assert(N < high * high);
    assert(high == low + 1);
    assert(N < (low + 1) * (low + 1));
    
    low
}

}