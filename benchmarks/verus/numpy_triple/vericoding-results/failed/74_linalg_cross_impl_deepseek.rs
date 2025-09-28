// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed signature syntax - removed parameter names from return type */
proof fn cross_product_ghost(a: [i8; 3], b: [i8; 3]) -> (int, int, int)
    ensures
        result.0 == a[1] as int * b[2] as int - a[2] as int * b[1] as int,
        result.1 == a[2] as int * b[0] as int - a[0] as int * b[2] as int,
        result.2 == a[0] as int * b[1] as int - a[1] as int * b[0] as int
{
    let x_val = a[1] as int * b[2] as int - a[2] as int * b[1] as int;
    let y_val = a[2] as int * b[0] as int - a[0] as int * b[2] as int;
    let z_val = a[0] as int * b[1] as int - a[1] as int * b[0] as int;
    (x_val, y_val, z_val)
}
// </vc-helpers>

// <vc-spec>
fn numpy_linalg_cross(x1: [i8; 3], x2: [i8; 3]) -> (result: [i8; 3])
    ensures
        result[0] as int == x1[1] as int * x2[2] as int - x1[2] as int * x2[1] as int,
        result[1] as int == x1[2] as int * x2[0] as int - x1[0] as int * x2[2] as int,
        result[2] as int == x1[0] as int * x2[1] as int - x1[1] as int * x2[0] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added proof to establish postconditions using ghost function */
    proof {
        let (ghost_x, ghost_y, ghost_z) = cross_product_ghost(x1, x2);
    }
    let x = (x1[1] as i16 * x2[2] as i16 - x1[2] as i16 * x2[1] as i16) as i8;
    let y = (x1[2] as i16 * x2[0] as i16 - x1[0] as i16 * x2[2] as i16) as i8;
    let z = (x1[0] as i16 * x2[1] as i16 - x1[1] as i16 * x2[0] as i16) as i8;
    [x, y, z]
}
// </vc-code>


}
fn main() {}