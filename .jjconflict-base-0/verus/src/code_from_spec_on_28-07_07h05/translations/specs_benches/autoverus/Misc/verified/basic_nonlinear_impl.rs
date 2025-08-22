use vstd::prelude::*;
fn main() {}

verus!{
     
//IMPL bound_check
/* code modified by LLM (iteration 4): simplified proof by using direct arithmetic reasoning */
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{
    /* code modified by LLM (iteration 4): direct proof using the fact that multiplication preserves ordering */
    assert(0xffff == 65535);
    assert(0x100000000 == 4294967296);
    assert(65535 * 65535 == 4294836225);
    assert(4294836225 < 4294967296);
    /* code modified by LLM (iteration 4): since x <= 65535 and y <= 65535, we have x*y <= 65535*65535 */
    assert(x * y <= 65535 * 65535) by {
        assert(x <= 65535);
        assert(y <= 65535);
    }
    /* code modified by LLM (iteration 4): chain the inequalities together */
    assert(x * y <= 65535 * 65535 == 4294836225 < 4294967296 == 0x100000000);
}
}