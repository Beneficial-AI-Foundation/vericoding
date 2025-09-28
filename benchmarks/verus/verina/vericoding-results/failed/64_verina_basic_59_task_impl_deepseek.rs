// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


proof fn double_spec_i32(x: i32) -> (result: int)
    ensures result == 2 * (x as int)
{
    2 * (x as int)
}

spec fn quadruple_spec_i32(x: i32) -> int {
    4 * (x as int)
}

proof fn safe_mul_2(x: i32) -> (result: i32)
    requires
        x >= i32::MIN / 2,
        x <= i32::MAX / 2,
    ensures result == 2 * x
{
    x * 2
}

// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add bounds checking and use safe multiplication helpers */
    let a: i32 = safe_mul_2(x);
    let b: i32 = safe_mul_2(a);
    
    proof {
        assert(a as int == 2 * (x as int));
        assert(b as int == 4 * (x as int));
    }
    
    (a, b)
}
// </vc-code>

}
fn main() {}