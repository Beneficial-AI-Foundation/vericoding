//from Verus tutorial

use vstd::prelude::*;
fn main() {}

verus!{
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{
    // The SMT solver can prove this arithmetic bound automatically
    // 0xffff * 0xffff = 0xfffe0001 < 0x100000000
}
}