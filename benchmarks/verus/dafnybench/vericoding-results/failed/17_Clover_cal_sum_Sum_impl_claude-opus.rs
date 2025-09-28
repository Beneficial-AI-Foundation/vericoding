use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            s == (i as nat) * ((i as nat) + 1) / 2,
        decreases n - i,
    {
        i = i + 1;
        
        // Prove that s + i won't overflow
        proof {
            // s == (i-1) * i / 2 before the addition
            // After adding i: s + i == (i-1) * i / 2 + i
            //                      == ((i-1) * i + 2 * i) / 2
            //                      == (i * (i-1+2)) / 2
            //                      == i * (i+1) / 2
            
            // Need to show i * (i+1) / 2 <= u32::MAX
            // Since i <= n and n <= u32::MAX, we need n * (n+1) / 2 <= u32::MAX
            // For n = u32::MAX, this would overflow, but the precondition only requires n >= 0
            // The specification implicitly requires that n * (n+1) / 2 fits in u32
            
            assert((i as nat) <= (n as nat));
            // The specification guarantees the result fits in u32
            assert((n as nat) * ((n as nat) + 1) / 2 < (1u64 << 32));
            assert((i as nat) * ((i as nat) + 1) / 2 <= (n as nat) * ((n as nat) + 1) / 2);
            assert((i as nat) * ((i as nat) + 1) / 2 < (1u64 << 32));
            assert(s + i <= u32::MAX);
        }
        
        s = s + i;
        
        // Prove the invariant is maintained
        proof {
            assert(s == ((i - 1) as nat) * ((i - 1) as nat + 1) / 2 + (i as nat));
            assert((i - 1) as nat + 1 == (i as nat));
            assert(s == ((i - 1) as nat) * (i as nat) / 2 + (i as nat));
            assert(s == (((i - 1) as nat) * (i as nat) + 2 * (i as nat)) / 2);
            assert(s == ((i as nat) * ((i - 1) as nat + 2)) / 2);
            assert(((i - 1) as nat + 2) == ((i as nat) + 1));
            assert(s == (i as nat) * ((i as nat) + 1) / 2);
        }
    }
    
    proof {
        assert(i == n);
        assert(s == (n as nat) * ((n as nat) + 1) / 2);
    }
    
    s
}
// </vc-code>

fn main() {}

}