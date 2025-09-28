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
fn helper_noop() {
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
    let n: nat = grid.len();
    let mut i: nat = 0;
    let mut total: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            total == sum_of_trips(grid@.map(|ii, row: Vec<i8>| row@.map(|jj, x: i8| x as int)).subrange(0, i), capacity as int),
        decreases n - i
    {
        let row: Vec<i8> = grid[i].clone();
        let m: nat = row.len();
        let mut j: nat = 0;
        let mut s: int = 0;
        while j < m
            invariant
                0 <= j && j <= m,
                s == sum_water(row@.map(|kk, x: i8| x as int).subrange(0, j)),
            decreases m - j
        {
            s = s + (row[j] as int);
            j = j + 1;
        }
        let trips: int = if s == 0 { 0 } else { (s + (capacity as int) - 1) / (capacity as int) };
        total = total + trips;
        i = i + 1;
    }
    let result: i8 = total as i8;
    result
}
// </vc-code>


}

fn main() {}