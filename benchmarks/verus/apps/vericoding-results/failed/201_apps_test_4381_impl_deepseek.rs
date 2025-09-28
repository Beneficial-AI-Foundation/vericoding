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
proof fn lemma_div2_even(n: int)
    requires
        n % 2 == 0,
    ensures
        (n / 2) * 2 == n,
{
    assert(n / 2 * 2 == n - n % 2);
    assert(n % 2 == 0);
}

proof fn lemma_i8_safe_arithmetic(train_fare_val: int, bus_fare_val: int)
    requires
        valid_input(train_fare_val, bus_fare_val),
    ensures
        (bus_fare_val / 2) <= 100,
        train_fare_val + (bus_fare_val / 2) <= 150,
        (bus_fare_val / 2) as i8 as int == bus_fare_val / 2,
        (train_fare_val + (bus_fare_val / 2)) as i8 as int == train_fare_val + (bus_fare_val / 2),
{
    assert(1 <= train_fare_val <= 100);
    assert(1 <= bus_fare_val <= 100);
    assert(bus_fare_val % 2 == 0);
    assert(bus_fare_val / 2 <= 50);
    assert(1 <= train_fare_val + (bus_fare_val / 2) <= 150);
    assert(-128 <= train_fare_val + (bus_fare_val / 2) <= 127);
}
// </vc-helpers>

// <vc-spec>
fn solve(train_fare: i8, bus_fare: i8) -> (result: i8)
    requires valid_input(train_fare as int, bus_fare as int)
    ensures result as int == total_cost(train_fare as int, bus_fare as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed lemma call and direct arithmetic */
    proof {
        lemma_div2_even(bus_fare as int);
        lemma_i8_safe_arithmetic(train_fare as int, bus_fare as int);
    }
    
    let total_cost = (train_fare as i16 + (bus_fare as i16 / 2)) as i8;
    total_cost
}
// </vc-code>


}

fn main() {}