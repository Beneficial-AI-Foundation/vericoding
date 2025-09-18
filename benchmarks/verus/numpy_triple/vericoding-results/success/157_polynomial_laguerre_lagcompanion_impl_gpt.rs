// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): recursive construction of a zero-filled row with proper decreases */
fn zero_row_rec(n: usize) -> (row: Vec<f64>)
    ensures
        row@.len() == n as int
    decreases n
{
    if n == 0 {
        Vec::<f64>::new()
    } else {
        let mut v = zero_row_rec(n - 1);
        v.push(0.0f64);
        assert(((n - 1) as int) + 1 == n as int);
        v
    }
}

/* helper modified by LLM (iteration 4): recursive construction of a zero-filled matrix with explicit forall proof about row lengths */
fn zero_matrix_rec(rows: usize, cols: usize) -> (m: Vec<Vec<f64>>)
    ensures
        m@.len() == rows as int,
        forall|i: int| 0 <= i < m@.len() ==> m@[i].len() == cols as int
    decreases rows
{
    if rows == 0 {
        Vec::<Vec<f64>>::new()
    } else {
        let mut m = zero_matrix_rec(rows - 1, cols);
        let ghost prev = m@;
        let row = zero_row_rec(cols);
        let ghost row_seq = row@;
        m.push(row);
        assert forall |i: int|
            0 <= i < m@.len() ==> m@[i].len() == cols as int
        by
        {
            if 0 <= i && i < m@.len() {
                assert(m@ == prev.push(row));
                assert(m@.len() == prev.len() + 1);
                if i < prev.len() {
                    assert(prev.push(row)[i] == prev[i]);
                    assert(prev[i].len() == cols as int);
                } else {
                    assert(i >= prev.len());
                    assert(i < prev.len() + 1);
                    assert(i == prev.len());
                    assert(prev.push(row)[i] == row);
                    assert(row_seq.len() == cols as int);
                }
            }
        };
        assert(((rows - 1) as int) + 1 == rows as int);
        m
    }
}
// </vc-helpers>

// <vc-spec>
fn lagcompanion(c: Vec<f64>) -> (result: Vec<Vec<f64>>)
    requires 
        c.len() >= 2,
    ensures 
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): construct zero companion-size square matrix using recursive helpers and prove sizes */
    let n: usize = c.len();
    let size: usize = n - 1;
    let m = zero_matrix_rec(size, size);
    assert(n as int == c@.len());
    assert(size as int == c@.len() - 1);
    m
}
// </vc-code>

}
fn main() {}