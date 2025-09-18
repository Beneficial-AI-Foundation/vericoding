// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added decreases clause to the loop. */
fn create_indices_vec(n: usize) -> (v: Vec<usize>)
    ensures v.len() == n,
            forall|i: int| 0 <= i < n ==> v[i] == i,
            forall|i: int, j: int| 0 <= i < j < n ==> v[i] < v[j]
{
    let mut v: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n,
                  v.len() == i,
                  forall|k: int| 0 <= k < i ==> v[k] == k,
                  forall|k: int, l: int| 0 <= k < l < i ==> v[k] < v[l]
        decreases n - i
    {
        v.push(i);
        i = i + 1;
    }
    v
}
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
/* code modified by LLM (iteration 4): No changes. */
{
    let mut grid = Vec::new();
    let inner_vec = create_indices_vec(n);
    grid.push(inner_vec);
    grid
}
// </vc-code>

}
fn main() {}