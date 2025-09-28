// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes to abs_i8. */
fn abs_i8(x: i8) -> (result: i8)
    ensures
        result >= 0,
        result == x || result == -x
{
    if x < 0 { -x } else { x }
}
// </vc-helpers>

// <vc-spec>
fn gcd_int(a: i8, b: i8) -> (result: i8)
    ensures
        result >= 0,
        (a as int) % (result as int) == 0,
        (b as int) % (result as int) == 0,
        forall|d: int| d > 0 && #[trigger] ((a as int) % d) == 0 && #[trigger] ((b as int) % d) == 0 ==> d <= (result as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected the trigger for the forall clause in the loop invariant. */
{
    let a_abs_val = abs_i8(a);
    let b_abs_val = abs_i8(b);

    if a_abs_val == 0i8 && b_abs_val == 0i8 {
        return 0i8;
    }

    let mut x: i8 = a_abs_val;
    let mut y: i8 = b_abs_val;

    while y != 0i8
        invariant
            x >= 0i8,
            y >= 0i8,
            forall|d: int| d > 0 && ((a_abs_val as int) % d == 0) && ((b_abs_val as int) % d == 0) <==> ((x as int) % d == 0) && ((y as int) % d == 0),
        decreases y
    {
        proof {
            assert((x as int) % (y as int) == (x % y) as int);
        }
        let remainder = x % y;
        x = y;
        y = remainder;
    }

    x
}
// </vc-code>


}
fn main() {}