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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn any_int(x: i8, y: i8, z: i8) -> (result: bool)
    ensures valid_result(x as int, y as int, z as int, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}