// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): addition preserves strict inequality */
proof fn lemma_add_preserves_lt(a: int, b: int, c: int)
    requires
        a < b,
    ensures
        a + c < b + c
{
    assert(a + c < b + c);
}

/* helper modified by LLM (iteration 5): multiplication monotonic w.r.t. nonnegative factor */
proof fn lemma_mul_mono_nonneg(a: int, b: int, c: int)
    requires
        a <= b,
        0 <= c,
    ensures
        a * c <= b * c
{
}

/* helper modified by LLM (iteration 5): structured proof that flattened index stays within total number of elements */
proof fn lemma_flatten_index_lt_total(row: usize, col: usize, rows: usize, cols: usize)
    requires
        row < rows,
        col < cols,
    ensures
        row * cols + col < rows * cols
{
    let r = row as int;
    let c = col as int;
    let R = rows as int;
    let C = cols as int;

    assert(0 <= r && r < R);
    assert(0 <= c && c < C);
    assert(0 < C) by {
        assert(0 <= c);
        assert(c < C);
    };

    // r*C + c < r*C + C since c < C
    lemma_add_preserves_lt(c, C, r * C);
    assert(r * C + c < r * C + C);

    // r*C + C == (r + 1) * C
    assert(r * C + C == (r + 1) * C);

    // (r + 1) * C <= R * C since r + 1 <= R and C >= 0
    assert(r + 1 <= R);
    lemma_mul_mono_nonneg(r + 1, R, C);
    assert((r + 1) * C <= R * C);

    // Conclude
    assert(r * C + c < (r + 1) * C);
    assert(r * C + c < R * C);
}
// </vc-helpers>

// <vc-spec>
fn ravel_multi_index(row_indices: &Vec<usize>, col_indices: &Vec<usize>, rows: usize, cols: usize) -> (result: Vec<usize>)
    requires 
        row_indices.len() == col_indices.len(),
        forall|i: int| 0 <= i < row_indices.len() ==> row_indices[i] < rows,
        forall|i: int| 0 <= i < col_indices.len() ==> col_indices[i] < cols,
    ensures 
        result.len() == row_indices.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == row_indices[i] * cols + col_indices[i] && 
            result[i] < rows * cols,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): strengthened invariants and localized proofs using helper lemma for bounds */
    let len = row_indices.len();
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            len == row_indices.len(),
            len == col_indices.len(),
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==>
                result@[j] == row_indices@[j] * cols + col_indices@[j] &&
                result@[j] < rows * cols,
        decreases len - i
    {
        let r = row_indices[i];
        let c = col_indices[i];

        proof {
            let ii: int = i as int;
            assert(0 <= ii && ii < len as int);
            assert(len == row_indices.len());
            assert(len == col_indices.len());
            assert(0 <= ii && ii < row_indices.len() as int);
            assert(0 <= ii && ii < col_indices.len() as int);
            assert(row_indices@[ii] == r);
            assert(col_indices@[ii] == c);
            assert(row_indices@[ii] < rows);
            assert(col_indices@[ii] < cols);
        }

        let flat = r * cols + c;
        let old_len = result.len();
        assert(old_len == i);
        result.push(flat);

        proof {
            let ii: int = i as int;
            assert(ii == old_len as int);
            assert(result@[ii] == flat);
            assert(row_indices@[ii] == r);
            assert(col_indices@[ii] == c);
            assert(flat == row_indices@[ii] * cols + col_indices@[ii]);
            lemma_flatten_index_lt_total(r, c, rows, cols);
            assert(result@[ii] < rows * cols);
        }

        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}