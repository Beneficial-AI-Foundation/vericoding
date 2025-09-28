// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(train_fare: int, bus_fare: int) -> bool {
    1 <= train_fare <= 100 && 1 <= bus_fare <= 100 && bus_fare % 2 == 0
}

spec fn total_cost(train_fare: int, bus_fare: int) -> int
    recommends valid_input(train_fare, bus_fare)
{
    train_fare + bus_fare / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate total_cost spec to int arithmetic */
proof fn total_cost_int_equiv(train: int, bus: int)
    requires valid_input(train, bus)
    ensures total_cost(train, bus) == train + bus / 2
{
    reveal(total_cost);
    assert(total_cost(train, bus) == train + bus / 2);
}
// </vc-helpers>

// <vc-spec>
fn solve(train_fare: i8, bus_fare: i8) -> (result: i8)
    requires valid_input(train_fare as int, bus_fare as int)
    ensures result as int == total_cost(train_fare as int, bus_fare as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute total in int to avoid i8 overflow and cast */
    let total: int = total_cost(train_fare as int, bus_fare as int);
    let result: i8 = total as i8;
    proof {
        total_cost_int_equiv(train_fare as int, bus_fare as int);
        assert(result as int == total_cost(train_fare as int, bus_fare as int));
    }
    result
}
// </vc-code>


}

fn main() {}