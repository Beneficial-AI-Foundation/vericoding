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
/* helper modified by LLM (iteration 5): Fixed compilation error by replacing is_empty with len() == 0 for slice length check */
exec fn sum_water_exec(well: &[i8]) -> (result: i8)
    requires
        true,
    ensures
        result as int == sum_water(well@.map(|i, x| x as int)),
    decreases well.len()
{
    if well.len() == 0 {
        0
    } else {
        well[0] + sum_water_exec(well.split_at(1).1)
    }
}

/* helper modified by LLM (iteration 5): Unchanged, no error */
exec fn trips_for_well_exec(well: &[i8], capacity: i8) -> (result: i8)
    requires
        capacity > 0,
    ensures
        result as int == trips_for_well(well@.map(|i, x| x as int), capacity as int),
    decreases well.len()
{
    let water_units = sum_water_exec(well);
    if water_units == 0 {
        0
    } else {
        (water_units + capacity - 1) / capacity
    }
}

/* helper modified by LLM (iteration 5): Fixed compilation error by replacing is_empty with len() == 0 for slice length check */
exec fn sum_of_trips_exec(grid: &[Vec<i8>], capacity: i8) -> (result: i8)
    requires
        valid_input(grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), capacity as int),
    ensures
        result as int == sum_of_trips(grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)), capacity as int),
    decreases grid.len()
{
    if grid.len() == 0 {
        0
    } else {
        let trips0 = trips_for_well_exec(&grid[0], capacity);
        trips0 + sum_of_trips_exec(grid.split_at(1).1, capacity)
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
    /* code modified by LLM (iteration 5): No change needed, helpers fixed */
    sum_of_trips_exec(grid.as_slice(), capacity)
}
// </vc-code>


}

fn main() {}