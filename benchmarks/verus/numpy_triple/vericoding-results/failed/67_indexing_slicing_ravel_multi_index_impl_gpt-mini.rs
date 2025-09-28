// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ravel bound lemma */
proof fn lemma_ravel_bound(r: nat, c: nat, rows: nat, cols: nat)
    requires
        r < rows,
        c < cols,
    ensures
        r * cols + c < rows * cols,
    decreases
        0usize,
{
    proof {
        assert(r <= rows - 1);
        assert(c <= cols - 1);
        assert(r * cols + c <= (rows - 1) * cols + (cols - 1));
        assert((rows - 1) * cols + (cols - 1) < rows * cols);
    }
}

// </vc-helpers>

// <vc-spec>
fn ravel_multi_index(row_indices: &Vec<u8>, col_indices: &Vec<u8>, rows: u8, cols: u8) -> (result: Vec<u8>)
    requires 
        row_indices.len() == col_indices.len(),
        forall|i: int| 0 <= i < row_indices.len() ==> (row_indices[i] as nat) < (rows as nat),
        forall|i: int| 0 <= i < col_indices.len() ==> (col_indices[i] as nat) < (cols as nat),
    ensures 
        result.len() == row_indices.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] as nat) == (row_indices[i] as nat) * (cols as nat) + (col_indices[i] as nat) && 
            (result[i] as nat) < (rows as nat) * (cols as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute flattened indices and prove bounds using lemma */
{
    let n = row_indices.len();
    let mut result: Vec<u8> = Vec::new();
    result.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let r: u8 = row_indices[i];
        let c: u8 = col_indices[i];
        let v_u16: u16 = (r as u16) * (cols as u16) + (c as u16);
        let v: u8 = v_u16 as u8;
        proof {
            let ii: int = i as int;
            let nn: int = n as int;
            assert(0 <= ii && ii < nn);
            assert((row_indices[ii] as nat) == (r as nat));
            assert((col_indices[ii] as nat) == (c as nat));
            assert((row_indices[ii] as nat) < (rows as nat));
            assert((col_indices[ii] as nat) < (cols as nat));
            lemma_ravel_bound((r as nat), (c as nat), (rows as nat), (cols as nat));
            assert((r as nat) * (cols as nat) + (c as nat) < (rows as nat) * (cols as nat));
            assert((v_u16 as nat) == (r as nat) * (cols as nat) + (c as nat));
            assert((v_u16 as nat) < (rows as nat) * (cols as nat));
        }
        result.push(v);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}