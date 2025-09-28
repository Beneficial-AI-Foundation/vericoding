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
proof fn lemma_sum_water_nonneg(well: Seq<int>)
    requires
        forall|i: int| 0 <= i < well.len() ==> well[i] >= 0
    ensures
        sum_water(well) >= 0
    decreases well.len()
{
    if well.len() == 0 {
    } else {
        lemma_sum_water_nonneg(well.subrange(1, well.len() as int));
    }
}

proof fn lemma_trips_nonneg(well: Seq<int>, capacity: int)
    requires
        capacity > 0,
        forall|i: int| 0 <= i < well.len() ==> well[i] >= 0
    ensures
        trips_for_well(well, capacity) >= 0
{
    lemma_sum_water_nonneg(well);
    let water_units = sum_water(well);
    if water_units == 0 {
    } else {
        assert((water_units + capacity - 1) / capacity >= 0);
    }
}

proof fn lemma_sum_of_trips_nonneg(grid: Seq<Seq<int>>, capacity: int)
    requires
        capacity > 0,
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> grid[i][j] >= 0
    ensures
        sum_of_trips(grid, capacity) >= 0
    decreases grid.len()
{
    if grid.len() == 0 {
    } else {
        lemma_trips_nonneg(grid[0], capacity);
        lemma_sum_of_trips_nonneg(grid.subrange(1, grid.len() as int), capacity);
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
    /* code modified by LLM (iteration 2): Added missing decreases clause to outer while loop */
    let mut total_trips: i8 = 0;
    let mut i: usize = 0;
    
    while i < grid.len()
        invariant
            0 <= i <= grid.len(),
            total_trips >= 0,
            total_trips as int == sum_of_trips(grid@.subrange(0, i as int).map(|idx, row: Vec<i8>| row@.map(|j, x: i8| x as int)), capacity as int),
            forall|idx: int, j: int| 0 <= idx < grid@.len() && 0 <= j < grid@[idx].len() ==> grid@[idx][j] >= 0,
        decreases grid.len() - i
    {
        let well = &grid[i];
        let mut water_units: i8 = 0;
        let mut j: usize = 0;
        
        while j < well.len()
            invariant
                0 <= j <= well.len(),
                water_units >= 0,
                water_units as int == sum_water(well@.subrange(0, j as int).map(|idx, x: i8| x as int)),
                well@ =~= grid@[i as int]@,
            decreases well.len() - j
        {
            water_units = water_units + well[j];
            j = j + 1;
        }
        
        assert(well@.subrange(0, well@.len() as int) =~= well@);
        assert(water_units as int == sum_water(well@.map(|idx, x: i8| x as int)));
        
        let trips_needed = if water_units == 0 {
            0
        } else {
            (water_units + capacity - 1) / capacity
        };
        
        assert(trips_needed as int == trips_for_well(grid@[i as int]@.map(|idx, x: i8| x as int), capacity as int));
        
        total_trips = total_trips + trips_needed;
        
        assert(grid@.subrange(0, (i + 1) as int) =~= grid@.subrange(0, i as int).push(grid@[i as int]));
        
        i = i + 1;
    }
    
    assert(grid@.subrange(0, grid@.len() as int) =~= grid@);
    
    total_trips
}
// </vc-code>


}

fn main() {}