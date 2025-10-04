// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn row_sum(row: Seq<nat>) -> nat
    decreases row.len()
{
    if row.len() == 0 {
        0
    } else {
        row[0] + row_sum(row.skip(1))
    }
}

spec fn grid_total_sum(grid: Seq<Seq<nat>>) -> nat
    decreases grid.len()
{
    if grid.len() == 0 {
        0
    } else {
        row_sum(grid[0]) + grid_total_sum(grid.skip(1))
    }
}

fn count_stars_in_region(grid: Vec<Vec<nat>>, x1: nat, y1: nat, x2: nat, y2: nat) -> (result: nat)
    requires 
        grid.len() > 0,
        forall|i: int| 0 <= i < grid.len() ==> grid[i].len() > 0,
        x1 >= 1 && y1 >= 1,
        x1 <= x2 && y1 <= y2,
    ensures
        true,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}