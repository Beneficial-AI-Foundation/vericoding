use vstd::prelude::*;

verus!{
//IMPL bound_check
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
    /* code modified by LLM (iteration 1): removed compilation error causing text and fixed proof structure */
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