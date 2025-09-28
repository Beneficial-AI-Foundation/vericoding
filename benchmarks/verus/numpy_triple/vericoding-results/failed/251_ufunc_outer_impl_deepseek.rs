// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type conversion from nat to usize using spec functions */
fn nat_to_usize(n: nat) -> (usize_n: usize)
    ensures usize_n == n as usize
{
    if n == 0 {
        0
    } else {
        let prev = nat_to_usize((n - 1) as nat);
        (prev + 1) as usize
    }
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
/* code modified by LLM (iteration 5): Fix vector indexing syntax and type conversions */
{
    let a_len = a.len();
    let b_len = b.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < a_len
        invariant
            i <= a_len,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == b_len,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < b_len ==> result[k][l] == op(a[k] as f64, b[l] as f64)
        decreases a_len - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < b_len
            invariant
                j <= b_len,
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row[l] == op(a[i] as f64, b[l] as f64)
            decreases b_len - j
        {
            let val = op(a[i] as f64, b[j] as f64);
            row.push(val);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}