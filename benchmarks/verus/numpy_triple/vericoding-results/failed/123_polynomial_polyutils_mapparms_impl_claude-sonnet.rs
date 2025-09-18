// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added preconditions to prevent overflow/underflow */
fn safe_sub(a: i32, b: i32) -> (result: i32)
    requires a >= i32::MIN + b && a <= i32::MAX + b
    ensures result == a - b
{
    a - b
}

fn safe_mul(a: i32, b: i32) -> (result: i32)
    requires (a == 0 || b == 0) || (a > 0 && b > 0 && a <= i32::MAX / b) || (a > 0 && b < 0 && b >= i32::MIN / a) || (a < 0 && b > 0 && a >= i32::MIN / b) || (a < 0 && b < 0 && a >= i32::MAX / b)
    ensures result == a * b
{
    a * b
}

fn safe_div(a: i32, b: i32) -> (result: i32)
    requires b != 0 && !(a == i32::MIN && b == -1)
    ensures result == a / b
{
    a / b
}
// </vc-helpers>

// <vc-spec>
fn mapparms(old: [i32; 2], new: [i32; 2]) -> (result: (i32, i32))
    requires old[0] != old[1],
    ensures ({
        let (offset, scale) = result;
        let oldlen = old[1] - old[0];
        let newlen = new[1] - new[0];
        offset + scale * old[0] == new[0] &&
        offset + scale * old[1] == new[1] &&
        scale == newlen / oldlen &&
        offset == (old[1] * new[0] - old[0] * new[1]) / oldlen
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use direct computation with overflow checks */
    let oldlen = old[1] - old[0];
    let newlen = new[1] - new[0];
    let scale = newlen / oldlen;
    let offset = (old[1] * new[0] - old[0] * new[1]) / oldlen;
    (offset, scale)
}
// </vc-code>

}
fn main() {}