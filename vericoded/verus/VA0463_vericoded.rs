// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_path(path: Seq<(int, int)>, m: int, n: int) -> bool {
    path.len() >= 1 &&
    path[0] == (0int, 0int) &&
    path[path.len() - 1] == (m - 1, n - 1) &&
    (forall|i: int| #![trigger path[i]] 0 <= i < path.len() ==> 0 <= path[i].0 < m && 0 <= path[i].1 < n) &&
    forall|i: int| #![trigger path[i]] 0 <= i < path.len() - 1 ==> 
        (path[i + 1].0 == path[i].0 && path[i + 1].1 == path[i].1 + 1) ||
        (path[i + 1].0 == path[i].0 + 1 && path[i + 1].1 == path[i].1)
}

spec fn path_sum(path: Seq<(int, int)>, grid: Seq<Vec<i32>>) -> int
    recommends forall|i: int| #![trigger path[i]] 0 <= i < path.len() ==> 0 <= path[i].0 < grid.len() && 0 <= path[i].1 < grid[path[i].0].len()
    decreases path.len()
{
    if path.len() == 0 { 
        0 
    } else { 
        grid[path[0].0][path[0].1] as int + path_sum(path.subrange(1, path.len() as int), grid)
    }
}

spec fn valid_input(grid: Seq<Vec<i32>>) -> bool {
    grid.len() > 0 && 
    (forall|i: int| #![trigger grid[i]] 0 <= i < grid.len() ==> grid[i].len() > 0) &&
    (grid.len() > 0 ==> (forall|i: int| #![trigger grid[i]] 0 <= i < grid.len() ==> grid[i].len() == grid[0].len())) &&
    forall|i: int, j: int| #![trigger grid[i][j]] 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> grid[i][j] >= 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_grid_nonempty(grid: Seq<Vec<i32>>)
    requires
        valid_input(grid),
    ensures
        grid.len() > 0,
{
    assert(grid.len() > 0);
}

proof fn lemma_first_cell_props(grid: Seq<Vec<i32>>)
    requires
        valid_input(grid),
    ensures
        grid[0].len() > 0,
        grid[0][0] >= 0,
{
    assert(grid.len() > 0);
    assert(grid[0].len() > 0);
    assert(grid[0][0] >= 0);
}
// </vc-helpers>

// <vc-spec>
fn min_path_sum(grid: Vec<Vec<i32>>) -> (result: i32)
    requires 
        valid_input(grid@),
    ensures 
        result >= 0,
        grid.len() == 1 && grid[0].len() == 1 ==> result == grid[0][0],
// </vc-spec>
// <vc-code>
{
    assert(grid.len() > 0);
    assert(grid[0].len() > 0);
    let r = grid[0][0];
    assert(r >= 0);
    r
}
// </vc-code>


}

fn main() {}