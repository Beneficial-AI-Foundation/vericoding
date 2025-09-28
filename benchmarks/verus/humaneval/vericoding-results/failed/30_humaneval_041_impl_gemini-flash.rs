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

// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The compiler error `The Verus types 'nat' and 'int' can only be used in ghost code ` indicates that `n_int` and `result_int` cannot be declared as `int` type in executable code. Changed `n_int` and `result_int` to `i8` type. */
    let n_i8: i8 = n;
    let result_i8: i8 = n_i8 * n_i8;
    result_i8
}
// </vc-code>


}

fn main() {}