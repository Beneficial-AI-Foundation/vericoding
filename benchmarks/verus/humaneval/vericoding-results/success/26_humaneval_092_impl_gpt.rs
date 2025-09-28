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
proof fn lemma_all_integers(x: int, y: int, z: int)
    ensures
        all_integers(x, y, z),
{
}

// </vc-helpers>

// <vc-spec>
fn any_int(x: i8, y: i8, z: i8) -> (result: bool)
    ensures valid_result(x as int, y as int, z as int, result)
// </vc-spec>
// <vc-code>
{
    let xi128: i128 = x as i128;
    let yi128: i128 = y as i128;
    let zi128: i128 = z as i128;

    let b: bool = xi128 == yi128 + zi128
        || yi128 == xi128 + zi128
        || zi128 == xi128 + yi128;

    proof {
        lemma_all_integers(x as int, y as int, z as int);
        assert(
            b == (
                (x as int) == (y as int) + (z as int)
                || (y as int) == (x as int) + (z as int)
                || (z as int) == (x as int) + (y as int)
            )
        );
    }

    b
}
// </vc-code>


}

fn main() {}