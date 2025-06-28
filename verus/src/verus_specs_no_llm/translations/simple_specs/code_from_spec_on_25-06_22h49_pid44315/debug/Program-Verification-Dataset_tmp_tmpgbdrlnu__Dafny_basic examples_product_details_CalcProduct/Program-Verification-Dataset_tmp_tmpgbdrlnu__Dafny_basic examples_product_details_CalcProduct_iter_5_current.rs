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
        // Prove that the multiplication won't overflow u32
        assert(m <= 0xFFFF);
        assert(n <= 0xFFFF);
        assert(0xFFFF == 65535);
        assert((m as nat) * (n as nat) <= (0xFFFF as nat) * (0xFFFF as nat));
        assert((0xFFFF as nat) * (0xFFFF as nat) == 65535nat * 65535nat);
        assert(65535nat * 65535nat == 4294836225nat);
        assert(4294836225nat <= 0xFFFFFFFFnat); // u32::MAX
        assert(0xFFFFFFFFnat == 4294967295nat);
        assert(4294836225nat <= 4294967295nat);
        
        // Therefore the multiplication fits in u32 and gives the correct mathematical result
        assert((m as nat) * (n as nat) <= 0xFFFFFFFFnat);
        assert(result == (m as nat) * (n as nat));
    }
    
    result
}

}