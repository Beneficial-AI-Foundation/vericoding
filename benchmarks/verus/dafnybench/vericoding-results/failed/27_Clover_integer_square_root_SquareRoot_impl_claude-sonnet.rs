use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish square root properties
proof fn lemma_sqrt_bounds(r: u32, n: u32)
    requires r * r <= n < (r + 1) * (r + 1)
    ensures r == 0 || (r - 1) * (r - 1) < r * r
{
    if r > 0 {
        assert((r - 1) * (r - 1) == r * r - 2 * r + 1);
        assert((r - 1) * (r - 1) < r * r);
    }
}

// Helper to check if multiplication will overflow
spec fn can_multiply(a: u32, b: u32) -> bool {
    a <= u32::MAX / b || b == 0
}

// Helper to safely compute square when possible
spec fn safe_square(x: u32) -> u32
    recommends x <= 65535
{
    (x as int * x as int) as u32
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    let mut low: u32 = 0;
    let mut high: u32 = 65536; // sqrt(u32::MAX) is approximately 65535
    
    // Find a better upper bound by doubling
    if n < (65536 as u64 * 65536 as u64) as u32 {
        let mut h = 1;
        while h <= 65535 && (h as u64 * h as u64) as u32 <= n
            invariant 
                h >= 1, 
                h <= 65536,
                h <= 65535 ==> (h as u64 * h as u64) as u32 <= n,
                h == 1 || (h / 2) <= 65535
            decreases 65536 - h
        {
            if h > 32767 { // Prevent overflow in h * 2
                break;
            }
            h = h * 2;
        }
        high = h;
    }
    
    // Binary search
    while low + 1 < high
        invariant 
            low <= 65535,
            high <= 65536,
            low < high,
            (low as u64 * low as u64) as u32 <= n,
            high > 65535 || (high as u64 * high as u64) as u32 > n
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if mid > 65535 {
            high = mid;
            continue;
        }
        
        let mid_squared = (mid as u64 * mid as u64) as u32;
        
        if mid_squared <= n {
            // Check if this could be the answer
            if mid == 65535 {
                assert((mid as u64 * mid as u64) as u32 <= n);
                assert(((mid + 1) as u64 * (mid + 1) as u64) as u32 > n); // Since mid + 1 = 65536 would overflow u32 range for squares
                return mid;
            }
            
            let next_squared = ((mid + 1) as u64 * (mid + 1) as u64) as u32;
            if next_squared > n {
                assert((mid as u64 * mid as u64) as u32 <= n < ((mid + 1) as u64 * (mid + 1) as u64) as u32);
                return mid;
            }
            low = mid;
        } else {
            high = mid;
        }
    }
    
    // At this point low + 1 >= high, so low == high - 1
    assert((low as u64 * low as u64) as u32 <= n);
    assert(high > 65535 || (high as u64 * high as u64) as u32 > n);
    
    if low == 65535 {
        return low;
    }
    
    // Check if low is the answer
    let next = low + 1;
    if ((next as u64 * next as u64) as u32) > n {
        return low;
    } else {
        return next;
    }
}
// </vc-code>

fn main() {}

}