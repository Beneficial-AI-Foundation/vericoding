// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn collision_count(n: int) -> int
    recommends valid_input(n)
{
    n * n
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result == collision_count(n) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect path for cast lemma */
proof fn lemma_square_i8(n: i8)
    requires
        n >= 0,
        (n as int) * (n as int) <= i8::MAX,
    ensures
        ((n as int) * (n as int)) as i8 as int == (n as int) * (n as int),
        (n as int) * (n as int) >= 0,
{
    let n_int = n as int;
    let result_int = n_int * n_int;
    vstd::arithmetic::mul::lemma_mul_nonnegative(n_int, n_int);
    assert(i8::MIN <= result_int && result_int <= i8::MAX);
    vstd::cast::lemma_int_as_i8(result_int);
}
// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): kept previous simple implementation to expose logic error */
    let result = (n as i16 * n as i16) as i8;
    result
}
// </vc-code>


}

fn main() {}