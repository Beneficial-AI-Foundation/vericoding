// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): provide safe identity sequence over ints to avoid usize cast/truncation issues */
spec fn id_seq_int(n: nat) -> Seq<int> { Seq::new(n, |k: int| k) }
proof fn id_seq_int_props(n: nat)
    ensures
        id_seq_int(n).len() == n,
        forall|i: int| 0 <= i < n ==> id_seq_int(n)[i] == i,
        forall|i: int, j: int| 0 <= i < j < n ==> id_seq_int(n)[i] < id_seq_int(n)[j]
{ }
/* helper modified by LLM (iteration 4): simple min function for potential use */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 4): loop builds increasing row [0..n-1] and proves equality and monotonicity */
    let mut row: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            row.len() == i,
            forall|k: int| 0 <= k < i as int ==> row@[k] as int == k,
            forall|a: int, b: int| 0 <= a < b < i as int ==> row@[a] < row@[b],
        decreases (n - i) as int
    {
        row.push(i);
        i = i + 1;
    }
    let mut grid: Vec<Vec<usize>> = Vec::new();
    grid.push(row);
    grid
}
// </vc-code>

}
fn main() {}