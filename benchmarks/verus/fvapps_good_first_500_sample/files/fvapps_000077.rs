// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_valid_grid(grid: Seq<Vec<char>>) -> bool {
    grid.len() > 0 && 
    forall|i: int| #![trigger grid[i]] 0 <= i < grid.len() ==> grid[i].len() == grid[0].len()
}

spec fn has_cross_at(grid: Seq<Vec<char>>, row: int, col: int) -> bool 
    recommends is_valid_grid(grid)
{
    0 <= row < grid.len() && 
    0 <= col < grid[0].len() &&
    forall|j: int| #![trigger grid[row][j]] 0 <= j < grid[0].len() ==> grid[row][j] == '*' &&
    forall|i: int| #![trigger grid[i][col]] 0 <= i < grid.len() ==> grid[i][col] == '*'
}

spec fn has_any_cross(grid: Seq<Vec<char>>) -> bool 
    recommends is_valid_grid(grid)
{
    exists|row: int, col: int| has_cross_at(grid, row, col)
}

fn min_minutes_for_cross(grid: Vec<Vec<char>>) -> (result: usize)
    requires 
        grid.len() > 0,
        grid.len() <= 50000,
        forall|i: int| #![trigger grid[i]] 0 <= i < grid.len() ==> grid[i].len() == grid[0].len(),
        grid[0].len() > 0,
        grid[0].len() <= 50000,
        is_valid_grid(grid@),
    ensures 
        result <= grid.len() + grid[0].len() - 1,
        has_any_cross(grid@) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}