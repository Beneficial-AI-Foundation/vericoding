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
fn sum_i8_vec_ref(vec: &Vec<i8>) -> (sum: i64)
    ensures sum as int == sum_water(vec@.map(|i, x| x as int))
{
    /* helper modified by LLM (iteration 3): changed return type to i64 and arithmetic operations */
    let mut s: i64 = 0;
    let mut i = 0;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            s as int == sum_water(vec@.subrange(0, i as int).map(|j, x| x as int)),
    {
        s += vec[i] as i64;
        i += 1;
    }
    s
}

fn trips_for_row_ref(row: &Vec<i8>, capacity: i8) -> (trips: i64)
    requires capacity > 0
    ensures trips as int == trips_for_well(row@.map(|i, x| x as int), capacity as int)
{
    /* helper modified by LLM (iteration 3): changed return type to i64 and arithmetic operations */
    let water = sum_i8_vec_ref(row);
    if water == 0 {
        0
    } else {
        (water + capacity as i64 - 1) / capacity as i64
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
    /* code modified by LLM (iteration 5): fixed invariant to avoid pattern matching in map closures */
    let mut total_trips: i64 = 0;
    let mut i = 0;
    while i < grid.len()
        invariant
            0 <= i <= grid.len(),
            total_trips as int == sum_of_trips(
                grid@.subrange(0, i as int).map(|j| grid@[j]@.map(|k| grid@[j]@[k] as int)),
                capacity as int
            ),
    {
        let row = &grid[i];
        total_trips += trips_for_row_ref(row, capacity);
        i += 1;
    }
    total_trips as i8
}
// </vc-code>


}

fn main() {}