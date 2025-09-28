// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed Vec indexing and type conversion */
use std::ops::{Index, IndexMut};

proof fn lemma_div_pos(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        a / b >= 0,
{
}

proof fn lemma_div_decreases(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        a / b <= a,
{
}

proof fn lemma_vec_len_positive<T>(v: Vec<T>)
    requires
        v@.len() >= 2,
    ensures
        v@.len() - 1 > 0,
{
}

fn create_zero_matrix(rows: u64, cols: u64) -> (result: Vec<Vec<f32>>)
    ensures
        result@.len() == rows,
        forall|i: int| 0 <= i < rows ==> result@[i].len() == cols,
        forall|i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> result@[i]@[j] == 0.0,
{
    let mut matrix: Vec<Vec<f32>> = Vec::new();
    let mut i: u64 = 0;
    while i < rows
        invariant
            i <= rows,
            matrix@.len() == i,
            forall|k: int| 0 <= k < i ==> matrix@[k].len() == cols,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < cols ==> matrix@[k]@[l] == 0.0,
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: u64 = 0;
        while j < cols
            invariant
                j <= cols,
                row@.len() == j,
                forall|k: int| 0 <= k < j ==> row@[k] == 0.0,
        {
            row.push(0.0);
            j = j + 1;
        }
        matrix.push(row);
        i = i + 1;
    }
    matrix
}

// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed type conversion from usize to int */
lemma_vec_len_positive(c);
let n = c.len() - 1;
let mut m = create_zero_matrix(n as u64, n as u64);

let mut i: u64 = 0;
while i < (n as u64)
    invariant
        i <= (n as u64),
        m@.len() == (n as u64),
        forall|k: int| 0 <= k < (n as u64) ==> m@[k].len() == (n as u64),
{
    if i < (n - 1) as u64 {
        let row_idx = i as usize;
        let col_idx = (i + 1) as usize;
        m[row_idx][col_idx] = 1.0;
    }
    
    let denom = -c[n as usize];
    proof { lemma_div_pos((c[i as usize] as int), (denom as int)); }
    
    let val = c[i as usize] / denom;
    let row_idx = (n - 1) as usize;
    let col_idx = i as usize;
    m[row_idx][col_idx] = val;
    
    i = i + 1;
}

m
}
// </vc-code>

}
fn main() {}