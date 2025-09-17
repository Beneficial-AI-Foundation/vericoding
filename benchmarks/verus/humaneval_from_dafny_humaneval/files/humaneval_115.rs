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

proof fn sum_water_slice_lemma(well: Seq<int>, j: int)
    requires 
        0 <= j < well.len()
    ensures sum_water(well.subrange(0, j + 1)) == sum_water(well.subrange(0, j)) + well[j]
{
    assume(false); /* TODO: Remove this line and implement the proof */
}

proof fn sum_water_full_slice_lemma(well: Seq<int>)
    ensures sum_water(well.subrange(0, well.len() as int)) == sum_water(well)
{
    assume(false); /* TODO: Remove this line and implement the proof */
}

proof fn sum_of_trips_slice_lemma(grid: Seq<Seq<int>>, i: int, capacity: int)
    requires 
        capacity > 0,
        0 <= i < grid.len()
    ensures sum_of_trips(grid.subrange(0, i + 1), capacity) == sum_of_trips(grid.subrange(0, i), capacity) + trips_for_well(grid[i], capacity)
{
    assume(false); /* TODO: Remove this line and implement the proof */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_fill(grid: Seq<Seq<int>>, capacity: int) -> (result: int)
    requires valid_input(grid, capacity)
    ensures 
        result >= 0,
        result == sum_of_trips(grid, capacity)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}