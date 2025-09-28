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
fn get_collision_count(n: i8) -> (count: int)
    requires valid_input(n as int)
    ensures count == collision_count(n as int)
{
    let n_int = n as int;
    n_int * n_int
}
// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    let count = get_collision_count(n);
    assert(count <= 127);
    count as i8
}
// </vc-code>


}

fn main() {}