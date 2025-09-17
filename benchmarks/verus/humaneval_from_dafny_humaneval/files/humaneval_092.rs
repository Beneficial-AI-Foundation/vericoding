// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn any_int(x: int, y: int, z: int) -> (result: bool)
    ensures valid_result(x, y, z, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}