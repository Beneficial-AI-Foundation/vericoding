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
        assert((0xFFFF as nat) * (0xFFFF as nat) == 0xFFFE0001nat);
        assert(0xFFFE0001nat <= 0xFFFFFFFFnat);
        assert((m as nat) * (n as nat) <= u32::MAX as nat);
    }
    m * n
}

}