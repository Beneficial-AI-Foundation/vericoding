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
        
        // Calculate the maximum value
        assert(65535nat * 65535nat == 4294836225nat);
        
        // Show this fits in u32 range (0 to 4,294,967,295)
        assert(4294836225nat <= 4294967295nat);
        assert(4294967295nat == 0xFFFFFFFFnat);
        
        // Since the mathematical product is within u32 bounds,
        // the u32 multiplication gives the correct mathematical result
        assert((m as nat) * (n as nat) <= 0xFFFFFFFFnat);
        assert(result as nat == (m as nat) * (n as nat));
    }
    
    result
}

}