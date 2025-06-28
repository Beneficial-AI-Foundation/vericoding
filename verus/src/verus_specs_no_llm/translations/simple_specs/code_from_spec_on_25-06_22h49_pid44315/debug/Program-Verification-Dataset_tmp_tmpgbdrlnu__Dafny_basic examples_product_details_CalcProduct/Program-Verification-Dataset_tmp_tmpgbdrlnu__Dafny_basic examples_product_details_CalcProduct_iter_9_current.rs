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
        
        // Convert to nat for reasoning about bounds
        assert((m as nat) <= 65535nat);
        assert((n as nat) <= 65535nat);
        
        // Show the product fits in u32
        assert((m as nat) * (n as nat) <= 65535nat * 65535nat);
        
        // Key calculation: 65535 * 65535 = 4,294,836,225
        // This is less than u32::MAX = 4,294,967,295
        calc! {
            (65535nat * 65535nat)
        <=  { /* 65535^2 = 4,294,836,225 < 2^32 */ }
            (4294967295nat)  // u32::MAX
        <   (4294967296nat)  // 2^32
        }
        
        // Since (m as nat) * (n as nat) fits in u32 range, 
        // the multiplication doesn't overflow
        assert((m as nat) * (n as nat) < 4294967296nat);
        
        // Use the fact that non-overflowing u32 multiplication 
        // preserves the mathematical result
        assert(mul_u32(m, n) == (m as nat) * (n as nat));
    }
    
    result
}

spec fn mul_u32(a: u32, b: u32) -> nat {
    (a as nat) * (b as nat)
}

}