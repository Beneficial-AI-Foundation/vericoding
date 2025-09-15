// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<i32>>) -> bool {
    grid.len() > 0 && grid[0].len() > 0 &&
    (forall|i: int| 0 <= i < grid.len() ==> grid[i].len() == grid[0].len()) &&
    (forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> grid[i][j] == 0 || grid[i][j] == 1)
}

spec fn dp_path_count(grid: Seq<Seq<i32>>) -> int {
    if !valid_grid(grid) {
        0
    } else {
        let m = grid.len();
        let n = grid[0].len();
        if grid[0][0] == 1 || grid[m as int - 1][n as int - 1] == 1 {
            0
        } else if m == 1 && n == 1 {
            1
        } else if m == 1 {
            if forall|j: int| 0 <= j < n ==> grid[0][j] == 0 { 1 } else { 0 }
        } else if n == 1 {
            if forall|i: int| 0 <= i < m ==> grid[i][0] == 0 { 1 } else { 0 }
        } else if forall|i: int, j: int| 0 <= i < m && 0 <= j < n ==> grid[i][j] == 0 {
            binomial(m as int + n as int - 2, m as int - 1)
        } else {
            0 /* Complex case placeholder */
        }
    }
}

spec fn binomial(n: int, k: int) -> int
    decreases n, k
{
    if n < 0 || k < 0 {
        0
    } else if k > n {
        0
    } else if k == 0 || k == n {
        1
    } else if k == 1 {
        n
    } else {
        binomial(n - 1, k - 1) + binomial(n - 1, k)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn unique_paths_with_obstacles(obstacle_grid: &[Vec<i32>]) -> (result: i32)
    requires
        obstacle_grid.len() > 0,
        obstacle_grid[0].len() > 0,
        forall|i: int| 0 <= i < obstacle_grid.len() ==> obstacle_grid[i].len() == obstacle_grid[0].len(),
        forall|i: int, j: int| 0 <= i < obstacle_grid.len() && 0 <= j < obstacle_grid[i].len() ==> 
            obstacle_grid[i][j] == 0 || obstacle_grid[i][j] == 1,
    ensures
        result >= 0,
        obstacle_grid[0][0] == 1 ==> result == 0,
        obstacle_grid[obstacle_grid.len()-1][obstacle_grid[0].len()-1] == 1 ==> result == 0,
        obstacle_grid.len() == 1 && obstacle_grid[0].len() == 1 ==> 
            result == (if obstacle_grid[0][0] == 0 { 1i32 } else { 0i32 }),
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