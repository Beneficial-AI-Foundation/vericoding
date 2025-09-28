// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers needed for this iteration */
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
    /* code modified by LLM (iteration 3): Strengthened loop invariant and added proof block to establish length postcondition */
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            v.len() == i,
            i <= n as usize,
            forall|k: int| 0 <= k < i ==> v@[k] == k as u8,
        decreases n as usize - i
    {
        v.push(i as u8);
        i = i + 1;
    }
    let mut grid: Vec<Vec<u8>> = Vec::new();
    grid.push(v);
    proof {
        assert(grid@[0].len() == v.len() as int);
        assert(v.len() as int == n as int);
    }
    grid
}
// </vc-code>

}
fn main() {}