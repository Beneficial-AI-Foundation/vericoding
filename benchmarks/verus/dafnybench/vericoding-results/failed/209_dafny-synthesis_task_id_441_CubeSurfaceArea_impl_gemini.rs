// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove intermediate value bounds */
proof fn lemma_square_in_i32_bounds(s: int)
    requires
        s > 0,
        6 * s * s <= i32::MAX as int,
    ensures
        s * s <= i32::MAX as int,
        s * s >= i32::MIN as int,
{
    assert(s * s >= 0) by(nonlinear_arith) requires s > 0;
    vstd::arithmetic::mul_le_mono_left(s * s, 1, 6);
}
// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper lemma to prove absence of overflow */
    lemma_square_in_i32_bounds(size as int);
    let square = size * size;
    let area = 6 * square;
    area
}
// </vc-code>

}
fn main() {}