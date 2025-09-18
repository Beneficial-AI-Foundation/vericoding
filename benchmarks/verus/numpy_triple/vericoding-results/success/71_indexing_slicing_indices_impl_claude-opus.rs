// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn indices(n: usize) -> (grid: Vec<Vec<usize>>)
    ensures 
        grid.len() == 1,
        grid[0].len() == n,
        forall|i: int| 0 <= i < n ==> grid[0][i] == i,
        forall|i: int, j: int| 0 <= i < j < n ==> grid[0][i] < grid[0][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assertion by ensuring loop completes correctly */
    let mut row: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            row@.len() == i as int,
            forall|j: int| 0 <= j < i ==> row@[j] == j,
            forall|j: int, k: int| 0 <= j < k < i ==> row@[j] < row@[k],
        decreases n - i
    {
        row.push(i);
        i = i + 1;
    }
    assert(i == n);
    assert(row@.len() == n as int);
    assert(forall|j: int| 0 <= j < n ==> row@[j] == j);
    let mut grid: Vec<Vec<usize>> = Vec::new();
    grid.push(row);
    assert(grid@.len() == 1);
    assert(grid@[0].len() == n as int);
    grid
}
// </vc-code>

}
fn main() {}