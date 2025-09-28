// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic lemmas about usize-to-int casts used in loop invariants */
proof fn usize_as_int_nonnegative(u: usize)
    ensures
        (u as int) >= 0,
{
    assert((u as int) >= 0);
}

/* helper modified by LLM (iteration 5): monotonicity of usize-to-int casts for loop progress proofs */
proof fn cast_usize_to_int_monotonic(u: usize, v: usize)
    ensures
        u <= v ==> (u as int) <= (v as int),
        u < v ==> (u as int) < (v as int),
{
    assert(u <= v ==> (u as int) <= (v as int));
    assert(u < v ==> (u as int) < (v as int));
}
// </vc-helpers>

// <vc-spec>
fn outer(op: spec_fn(f64, f64) -> f64, a: Vec<f64>, b: Vec<f64>) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
            result[i][j] == op(a[i], b[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct rows using choose to match spec op and maintain invariants */
    let n_a = a.len();
    let n_b = b.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_a
        invariant
            i <= n_a,
            result.len() == i,
            forall|ii: int| 0 <= ii < i as int ==> result[ii].len() == n_b,
            forall|ii: int, jj: int|
                0 <= ii < i as int && 0 <= jj < n_b as int ==> result[ii][jj] == op(a[ii], b[jj]),
        decreases (n_a - i) as int
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < n_b
            invariant
                j <= n_b,
                row.len() == j,
                forall|jj: int| 0 <= jj < j as int ==> row[jj] == op(a[i], b[jj]),
            decreases (n_b - j) as int
        {
            let val: f64 = choose|v: f64| v == op(a[i], b[j]);
            row.push(val);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}