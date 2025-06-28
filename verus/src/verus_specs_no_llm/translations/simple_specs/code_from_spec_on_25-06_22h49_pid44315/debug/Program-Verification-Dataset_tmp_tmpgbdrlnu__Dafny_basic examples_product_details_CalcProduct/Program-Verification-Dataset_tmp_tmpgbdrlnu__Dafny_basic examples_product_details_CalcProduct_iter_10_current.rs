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
        // The key insight is that with the given bounds, multiplication won't overflow
        // m <= 0xFFFF = 65535, n <= 0xFFFF = 65535
        // So m * n <= 65535 * 65535 = 4,294,836,225
        // This is less than u32::MAX = 4,294,967,295, so no overflow occurs
        
        assert(m <= 0xFFFF);
        assert(n <= 0xFFFF);
        assert(0xFFFF == 65535);
        
        // When no overflow occurs in u32 multiplication,
        // the result equals the mathematical product
        assert((m as nat) <= 65535);
        assert((n as nat) <= 65535);
        assert((m as nat) * (n as nat) <= 65535 * 65535);
        assert(65535 * 65535 == 4294836225);
        assert(4294836225 <= 4294967295); // u32::MAX
        
        // Since the mathematical product fits in u32, 
        // the u32 multiplication gives the correct mathematical result
        assert(result == (m as nat) * (n as nat));
    }
    
    result
}

}