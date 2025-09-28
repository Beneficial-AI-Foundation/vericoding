use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut r: u32 = 0;
    
    loop
        invariant
            r >= 0,
            (r as int) * (r as int) <= n as int,
        decreases (n as int) - (r as int) * (r as int),
    {
        // Check if we've reached the maximum possible value for r
        if r == u32::MAX {
            // If r = u32::MAX, then r² ≤ n and (r+1) would overflow
            // This means we've found our answer
            assert((r as int) * (r as int) <= n as int);
            return r;
        }
        
        // At this point, r < u32::MAX, so r + 1 won't overflow u32
        assert(r < u32::MAX);
        let r_plus_1 = (r + 1) as u32;
        
        // Use u64 to avoid overflow in the multiplication
        let r_plus_1_u64 = r_plus_1 as u64;
        
        // Since r < u32::MAX, we have r + 1 <= u32::MAX
        // Therefore (r+1)² <= (2^32)² = 2^64, which fits in u64
        assert(r_plus_1_u64 <= u32::MAX as u64);
        let next_square_u64 = r_plus_1_u64 * r_plus_1_u64;
        
        // Establish the connection between the u64 computation and the int computation
        assert(r_plus_1_u64 as int == (r + 1) as int);
        assert(next_square_u64 as int == (r_plus_1_u64 as int) * (r_plus_1_u64 as int));
        assert(next_square_u64 as int == ((r + 1) as int) * ((r + 1) as int));
        
        if next_square_u64 > n as u64 {
            // Found the answer: r² ≤ n < (r+1)²
            assert((r as int) * (r as int) <= n as int);
            assert(((r + 1) as int) * ((r + 1) as int) == next_square_u64 as int);
            assert(next_square_u64 as int > n as int);
            return r;
        }
        
        // Continue searching: we know (r+1)² ≤ n
        assert(next_square_u64 <= n as u64);
        assert(((r + 1) as int) * ((r + 1) as int) <= n as int);
        r = r + 1;
        
        // For the decreases clause: the square increases, so the gap decreases
        assert((r as int) * (r as int) > ((r - 1) as int) * ((r - 1) as int));
    }
}
// </vc-code>

fn main() {}

}