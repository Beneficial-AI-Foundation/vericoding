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
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}