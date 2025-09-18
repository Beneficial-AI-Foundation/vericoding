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
    /* code modified by LLM (iteration 2): added a decreases clause to the while loop to prove termination */
    let mut row = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            row.len() == i,
            forall|j: int| 0 <= j < i ==> row@[j] == j,
        decreases n - i
    {
        row.push(i);
        i = i + 1;
    }

    let mut grid = Vec::new();
    grid.push(row);
    grid
}
// </vc-code>

}
fn main() {}