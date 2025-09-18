// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): strengthened loop invariant to ensure final length and preserved per-index property for identity row */
fn make_row(n: usize, diag: usize) -> (row: Vec<f32>)
    requires
        diag < n,
    ensures
        row.len() == n,
        forall|j: int| 0 <= j < n ==> #[trigger] row@[j] == if j == diag as int { 1.0f32 } else { 0.0f32 }
{
    let mut row: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            row.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] row@[k] == if k == diag as int { 1.0f32 } else { 0.0f32 }
        decreases n - j
    {
        let v: f32 = if j == diag { 1.0f32 } else { 0.0f32 };
        row.push(v);
        j += 1;
    }
    proof {
        assert(j >= n);
        assert(j <= n);
        assert(j == n);
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn eye(n: usize) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == if i == j { 1.0f32 } else { 0.0f32 },
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == result[j][i],
        forall|i: int, j:int| 0 <= i <= j < n ==> (#[trigger] result[i][j] == 1.0f32 ==> i == j),
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> 
            result[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added i <= n invariant to conclude final length; build each row with make_row preserving identity structure */
    let mut m: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            m.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] m@[p].len() == n,
            forall|p: int, j: int| 0 <= p < i && 0 <= j < n ==> #[trigger] m@[p]@[j] == if p == j { 1.0f32 } else { 0.0f32 }
        decreases n - i
    {
        let row = make_row(n, i);
        m.push(row);
        i += 1;
    }
    proof {
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
    }
    m
}
// </vc-code>

}
fn main() {}