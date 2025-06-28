use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcProduct(m: u32, n: u32) -> (res: u32)
    requires
        m <= 0xFFFF,
        n <= 0xFFFF,
    ensures
        res == (m as nat) * (n as nat)
{
    proof {
        // Prove that the multiplication won't overflow
        assert(m <= 0xFFFF);
        assert(n <= 0xFFFF);
        assert((m as nat) * (n as nat) <= (0xFFFF as nat) * (0xFFFF as nat));
        // 0xFFFF * 0xFFFF = 65535 * 65535 = 4294836225 = 0xFFFE0001
        // But 0xFFFE0001 > 0xFFFFFFFF (u32::MAX), so this would overflow
        // However, since we're doing the multiplication in u32 arithmetic,
        // we need to ensure the result fits in u32
        assert(0xFFFF == 65535);
        assert(65535 * 65535 == 4294836225);
        assert(4294836225 <= 4294967295); // This is actually false!
        
        // The issue is that 0xFFFF * 0xFFFF does overflow u32
        // We need to use a different approach
    }
    
    // Use u64 for intermediate calculation to avoid overflow
    let result = (m as u64) * (n as u64);
    proof {
        assert(result == (m as nat) * (n as nat));
        assert(m <= 0xFFFF);
        assert(n <= 0xFFFF);
        assert((m as nat) * (n as nat) <= (0xFFFF as nat) * (0xFFFF as nat));
        assert((0xFFFF as nat) * (0xFFFF as nat) < 0x100000000nat); // This is false
    }
    result as u32
}

}