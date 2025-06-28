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
    let result = m * n;
    
    proof {
        // Establish the bounds
        assert(m <= 0xFFFF);
        assert(n <= 0xFFFF);
        assert(0xFFFF == 65535);
        
        // Convert to nat for reasoning
        assert((m as nat) <= 65535nat);
        assert((n as nat) <= 65535nat);
        
        // The key insight: we need to show that m * n doesn't overflow
        // The maximum possible value is 65535 * 65535 = 4,294,836,225
        assert((m as nat) * (n as nat) <= 65535nat * 65535nat);
        
        // Calculate the maximum value - this needs to be computed step by step
        // 65535 * 65535 = 4,294,836,225
        // We can verify this is less than u32::MAX = 4,294,967,295
        assert(65535nat * 65535nat < 4294967296nat); // 2^32
        
        // Since the product fits in u32 range and doesn't overflow,
        // the u32 multiplication preserves the mathematical result
        // This is a built-in property in Verus for non-overflowing operations
        assert((m * n) as nat == (m as nat) * (n as nat));
    }
    
    result
}

}