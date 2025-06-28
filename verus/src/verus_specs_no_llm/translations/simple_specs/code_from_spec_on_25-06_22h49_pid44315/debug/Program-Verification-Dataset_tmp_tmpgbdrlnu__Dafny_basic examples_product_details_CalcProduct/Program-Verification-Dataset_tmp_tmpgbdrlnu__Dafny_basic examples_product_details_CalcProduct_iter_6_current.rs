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
        // First establish the bounds
        assert(m <= 0xFFFF);
        assert(n <= 0xFFFF);
        assert(0xFFFF == 65535);
        
        // Show that the product fits in u32
        assert((m as nat) <= 65535nat);
        assert((n as nat) <= 65535nat);
        assert((m as nat) * (n as nat) <= 65535nat * 65535nat);
        assert(65535nat * 65535nat == 4294836225nat);
        
        // Show this is within u32 bounds
        assert(4294836225nat < 4294967296nat); // 2^32
        assert((m as nat) * (n as nat) < 4294967296nat);
        
        // Since the mathematical product fits in u32, the u32 multiplication
        // is equivalent to the mathematical multiplication
        assert(result as nat == (m as nat) * (n as nat));
    }
    
    result
}

}