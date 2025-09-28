// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(grid: Seq<Seq<int>>, capacity: int) -> bool {
    capacity > 0
}

spec fn sum_water(well: Seq<int>) -> int
    decreases well.len()
{
    if well.len() == 0 {
        0
    } else {
        well[0] + sum_water(well.subrange(1, well.len() as int))
    }
}

spec fn trips_for_well(well: Seq<int>, capacity: int) -> int {
    let water_units = sum_water(well);
    if water_units == 0 {
        0
    } else {
        (water_units + capacity - 1) / capacity
    }
}

spec fn sum_of_trips(grid: Seq<Seq<int>>, capacity: int) -> int
    decreases grid.len()
{
    if grid.len() == 0 {
        0
    } else {
        trips_for_well(grid[0], capacity) + sum_of_trips(grid.subrange(1, grid.len() as int), capacity)
    }
}


// </vc-preamble>

// <vc-helpers>

proof fn validate_trips_calculation(well: Seq<int>, capacity: int)
    requires
        capacity > 0,
        well.forall(|x| x >= 0),
    ensures
        trips_for_well(well, capacity) == {
            let total = sum_water(well);
            if total == 0 { 0 } else { (total + capacity - 1) / capacity }
        },
{
    let total = sum_water(well);
    if total == 0 {
        assert(trips_for_well(well, capacity) == 0);
    } else {
        assert(total > 0);
        assert((total + capacity - 1) / capacity >= 1);
        assert(trips_for_well(well, capacity) == (total + capacity - 1) / capacity);
    }
}

proof fn sum_water_nonrecursive_equals_recursive(well: Seq<int>)
    ensures
        sum_water_nonrecursive(well) == sum_water(well),
{
    sum_water_nonrecursive_equals_recursive_helper(well, 0);
}

proof fn sum_water_nonrecursive_equals_recursive_helper(well: Seq<int>, i: nat)
    requires
        i <= well.len(),
    ensures
        well.subrange(0, i as int).sum() == sum_water(well.subrange(0, i as int)),
{
    if i < well.len() {
        sum_water_nonrecursive_equals_recursive_helper(well, i + 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn max_fill(grid: Vec<Vec<i8>>, capacity: i8) -> (result: i8)
    requires valid_input(grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), capacity as int)
    ensures 
        result >= 0,
        result as int == sum_of_trips(grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), capacity as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing 'let cap' and using proper ghost operations */
    let capacity_int = capacity as int;
    let mut total_trips = 0;
    
    let mut i = 0;
    while i < grid.len()
        invariant
            i <= grid.len(),
            total_trips >= 0,
            total_trips == sum_of_trips(grid@.map(|idx, row: Vec<i8>| row@.map(|j, x: i8| x as int)).subrange(0, i as int), capacity_int),
    {
        ghost {
            let well_spec = grid@[i].map(|j, x: i8| x as int);
            let water_units = sum_water(well_spec);
            
            if water_units == 0 {
                // No trips needed
            } else {
                let trips = (water_units + capacity_int - 1) / capacity_int;
                total_trips += trips;
            }
        }
        
        i += 1;
    }
    
    total_trips as i8
}
// </vc-code>


}

fn main() {}