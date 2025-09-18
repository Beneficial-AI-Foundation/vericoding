// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define lower-triangular element selection from flat index */
spec fn lower_val_for_index(m: Seq<f32>, n: nat, k: nat) -> f32
    recommends m.len() == n * n, n > 0, k < n * n
{
    let i = k / n;
    let j = k % n;
    if i < n && j < n && i >= j { m[k] } else { 0.0f32 }
}

/* helper modified by LLM (iteration 2): construct tril sequence view from matrix view */
spec fn tril_seq(m: Seq<f32>, n: nat) -> Seq<f32>
    recommends m.len() == n * n, n > 0
{
    Seq::new(n * n, |k: int| {
        lower_val_for_index(m, n, k as nat)
    })
}

/* helper modified by LLM (iteration 2): arithmetic lemma for div/mod on i*n + j */
proof fn lemma_div_mod_mul_add(i: nat, j: nat, n: nat)
    requires n > 0, j < n
    ensures
        ((i * n + j) / n) == i,
        ((i * n + j) % n) == j
{
}

/* helper modified by LLM (iteration 2): index bound lemma for flat indexing */
proof fn lemma_idx_lt_len(i: nat, j: nat, n: nat)
    requires i < n, j < n, n > 0
    ensures i * n + j < n * n
{
}
// </vc-helpers>

// <vc-spec>
fn tril(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        n > 0,
        matrix.len() == n * n,
    ensures
        result.len() == matrix.len(),
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == matrix[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use ghost view and nat for spec computations, then build Vec from spec sequence */
    let ghost m = matrix@;
    let ghost n_nat: nat = n as nat;
    let result: Vec<f32> = Vec::from_seq(tril_seq(m, n_nat));
    result
}
// </vc-code>

}
fn main() {}