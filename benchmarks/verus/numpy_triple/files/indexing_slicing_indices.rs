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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}