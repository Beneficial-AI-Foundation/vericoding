
use vstd::prelude::*;

verus!{
proof fn bound_check(x: u32, y: u32)
    // pre-conditions-start
    requires
        x <= 0xffff,
        y <= 0xffff,
    // pre-conditions-end
    // post-conditions-start
    ensures
        x*y <= 0x100000000,
    // post-conditions-end
{
    // impl-start
    assert(x * y <= 0x100000000) by(nonlinear_arith)
        requires
            x <= 0xffff,
            y <= 0xffff,
    {
    }
    // impl-end
}
// pure-end
}
fn main() {}
