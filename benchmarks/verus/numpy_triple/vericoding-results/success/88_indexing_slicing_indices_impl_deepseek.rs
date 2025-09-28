// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn indices_helper(n: u8, i: u8, grid: &mut Vec<u8>)
    requires
        n > 0,
        i <= n,
        old(grid).len() == i as nat,
        forall|k: int| 0 <= k < i as int ==> old(grid)@[k] == k as u8,
        forall|k: int, l: int| 0 <= k < l < i as int ==> old(grid)@[k] < old(grid)@[l],
    ensures
        grid.len() == n as nat,
        forall|k: int| 0 <= k < n as int ==> grid@[k] == k as u8,
        forall|k: int, l: int| 0 <= k < l < n as int ==> grid@[k] < grid@[l],
    decreases (n - i) as int
{
    if i < n {
        grid.push(i);
        assert(grid@.len() == (i + 1) as nat);
        indices_helper(n, i + 1, grid);
    }
}

/* helper modified by LLM (iteration 2): Fixed old(grid) references in requires clause */

// </vc-helpers>

// <vc-spec>
fn indices(n: u8) -> (grid: Vec<Vec<u8>>)
    ensures 
        grid.len() == 1,
        grid@[0].len() == n as nat,
        forall|i: int| 0 <= i < n as int ==> grid@[0][i] == i as u8,
        forall|i: int, j: int| 0 <= i < j < n as int ==> grid@[0][i] < grid@[0][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added handling for n=0 case and proper initialization */
    let mut grid: Vec<Vec<u8>> = Vec::new();
    let mut inner: Vec<u8> = Vec::new();
    if n == 0 {
        grid.push(inner);
    } else {
        indices_helper(n, 0, &mut inner);
        grid.push(inner);
    }
    grid
}
// </vc-code>

}
fn main() {}