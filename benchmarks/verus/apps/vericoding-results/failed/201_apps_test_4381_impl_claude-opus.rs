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
fn solve(train_fare: i8, bus_fare: i8) -> (result: i8)
    requires valid_input(train_fare as int, bus_fare as int)
    ensures result as int == total_cost(train_fare as int, bus_fare as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added overflow prevention by using wider type and explicit bounds check */
    let half_bus_fare = bus_fare / 2;
    
    // Prove properties about half_bus_fare
    assert(half_bus_fare as int == bus_fare as int / 2);
    assert(bus_fare as int <= 100);
    assert(half_bus_fare as int <= 50);
    
    // Use i32 to avoid overflow, then convert back
    let train_fare_i32: i32 = train_fare as i32;
    let half_bus_fare_i32: i32 = half_bus_fare as i32;
    let result_i32 = train_fare_i32 + half_bus_fare_i32;
    
    // Prove bounds
    assert(train_fare as int >= 1 && train_fare as int <= 100);
    assert(half_bus_fare as int >= 0 && half_bus_fare as int <= 50);
    assert(result_i32 as int == train_fare as int + half_bus_fare as int);
    assert(result_i32 as int >= 1 && result_i32 as int <= 150);
    assert(result_i32 <= 127);
    
    let result: i8 = result_i32 as i8;
    
    // Prove the postcondition
    assert(result as int == result_i32 as int);
    assert(result as int == train_fare as int + half_bus_fare as int);
    assert(result as int == train_fare as int + bus_fare as int / 2);
    assert(result as int == total_cost(train_fare as int, bus_fare as int));
    
    result
}
// </vc-code>


}

fn main() {}