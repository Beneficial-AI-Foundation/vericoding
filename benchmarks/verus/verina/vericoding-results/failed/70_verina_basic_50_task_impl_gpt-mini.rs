// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove abs is non-negative */
proof fn abs_nonneg(n: int)
    ensures
        abs(n) >= 0,
{
    if n >= 0 {
        assert(abs(n) == n);
        assert(abs(n) >= 0);
    } else {
        assert(abs(n) == -n);
        assert(abs(n) >= 0);
    }
}

/* helper modified by LLM (iteration 5): cancellation law for i32 addition and subtraction */
proof fn i32_add_sub_cancel(x: i32)
    ensures
        x + (0i32 - x) == 0i32,
{
    assert(x + (0i32 - x) == 0i32);
}

// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use subtraction 0 - x to implement negation without calling wrapping_neg in proofs */
    let result: i32;
    if x >= 0 {
        result = x;
    } else {
        result = 0i32 - x;
        proof {
            i32_add_sub_cancel(x);
        }
    }
    result
}

// </vc-code>

}
fn main() {}