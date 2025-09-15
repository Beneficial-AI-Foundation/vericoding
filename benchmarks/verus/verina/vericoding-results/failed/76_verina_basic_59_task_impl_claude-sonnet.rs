// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn safe_mul(a: i32, b: i32) -> bool { a.checked_mul(b).is_some() }

/* helper modified by LLM (iteration 5): added safety check for multiplication */
spec fn in_safe_range(x: i32) -> bool {
    x >= i32::MIN / 4 && x <= i32::MAX / 4
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
    /* code modified by LLM (iteration 5): used int type to avoid overflow */
    let doubled = 2int * (x as int);
    let quadrupled = 2int * doubled;
    ((doubled as i32), (quadrupled as i32))
}
// </vc-code>

}
fn main() {}