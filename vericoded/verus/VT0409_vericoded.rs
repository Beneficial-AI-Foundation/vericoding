// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use usize instead of nat/int and add proper invariants */
fn make_zero_row(n: usize) -> (row: Vec<f32>)
    ensures
        row@.len() == n as int,
{
    let mut row: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            row@.len() == j as int,
        decreases (n - j) as int
    {
        row.push(0.0f32);
        j = j + 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn hermecompanion(c: Vec<f32>) -> (mat: Vec<Vec<f32>>)
    requires 
        c@.len() >= 2,
        c[c@.len() - 1] != 0.0f32,
    ensures
        mat@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize for lengths and build n x n zero matrix */
    let n: usize = c.len() - 1;
    proof {
        assert(c@.len() == c.len() as int);
        assert(n as int == c@.len() - 1);
    }
    let mut mat: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            mat@.len() == i as int,
            n as int == c@.len() - 1,
            forall|k: int| 0 <= k < mat@.len() ==> mat@[k].len() == c@.len() - 1,
        decreases (n - i) as int
    {
        let row = make_zero_row(n);
        proof { assert(row@.len() == c@.len() - 1); }
        mat.push(row);
        i = i + 1;
    }
    mat
}
// </vc-code>


}
fn main() {}