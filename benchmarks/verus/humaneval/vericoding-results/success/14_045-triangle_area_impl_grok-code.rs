// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triangle_area(a: u64, h: u64) -> (area: u64)

    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,

    ensures
        area == a * h / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use u128 for safe multiplication to avoid overflow */
    ((a as u128 * h as u128) / 2) as u64
}
// </vc-code>

}
fn main() {}