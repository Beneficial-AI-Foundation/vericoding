// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_integer(x: int) -> bool {
    true
}

spec fn all_integers(x: int, y: int, z: int) -> bool {
    is_integer(x) && is_integer(y) && is_integer(z)
}

spec fn one_equals_sum_of_other_two(x: int, y: int, z: int) -> bool {
    x == y + z || y == x + z || z == x + y
}

spec fn valid_result(x: int, y: int, z: int, result: bool) -> bool {
    result <==> (all_integers(x, y, z) && one_equals_sum_of_other_two(x, y, z))
}

// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn any_int(x: i8, y: i8, z: i8) -> (result: bool)
    ensures valid_result(x as int, y as int, z as int, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Use i16 to avoid overflow in sum checks for correct arithmetic */
    let x_i16 = x as i16;
    let y_i16 = y as i16;
    let z_i16 = z as i16;
    (x_i16 == y_i16 + z_i16) || (y_i16 == x_i16 + z_i16) || (z_i16 == x_i16 + y_i16)
}
// </vc-code>


}

fn main() {}