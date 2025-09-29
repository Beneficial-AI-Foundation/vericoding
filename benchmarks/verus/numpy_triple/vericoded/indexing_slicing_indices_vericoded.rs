// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed loop invariant for `n - i` and `i as nat` */
fn create_row(n: u8) -> (row: Vec<u8>)
    ensures
        row.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==> row@[i] == i as u8,
        forall|i: int, j: int| 0 <= i < j < n as int ==> row@[i] < row@[j],
{
    let mut row_vec: Vec<u8> = Vec::new();
    let mut i: u8 = 0;
    while i < n
        invariant
            row_vec.len() == i as nat,
            i <= n,
            forall|k: int| 0 <= k < i as int ==> row_vec@[k] == k as u8,
            forall|k: int, l: int| 0 <= k < l < i as int ==> row_vec@[k] < row_vec@[l],
        decreases n - i
    {
        row_vec.push(i);
        i = i + 1;
    }
    row_vec
}
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
/* code modified by LLM (iteration 2): added post-condition checks */
{
    let row = create_row(n);
    let mut grid: Vec<Vec<u8>> = Vec::new();
    grid.push(row);
    grid
}
// </vc-code>

}
fn main() {}