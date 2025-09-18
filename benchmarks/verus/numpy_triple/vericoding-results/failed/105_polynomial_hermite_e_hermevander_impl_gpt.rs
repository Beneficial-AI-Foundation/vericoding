// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed int/usize indexing by using int indices and proper decreases */
fn build_row(val: f64, deg: usize) -> (result: Vec<f64>)
    ensures
        result.len() == deg + 1,
        result[0int] == 1.0,
        deg > 0 ==> result[1int] == val
{
    let mut row: Vec<f64> = Vec::new();
    row.push(1.0);
    if deg > 0 {
        row.push(val);
    }
    while row.len() < deg + 1
        invariant
            row.len() <= deg + 1,
            row.len() > 0,
            row[0int] == 1.0,
            deg > 0 ==> row.len() >= 2,
            deg > 0 ==> row[1int] == val
        decreases ((deg + 1 - row.len()) as int)
    {
        row.push(0.0);
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int/usize mismatches by using int indices in assertions/invariants */
    let n = x.len();
    let mut result_vec: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> result_vec[j].len() == deg + 1,
            forall|j: int| 0 <= j < i as int ==> result_vec[j][0int] == 1.0,
            deg > 0 ==> forall|j: int| 0 <= j < i as int ==> result_vec[j][1int] == x[j]
        decreases ((n - i) as int)
    {
        let idx_i: int = i as int;
        let xi = x[i];
        let row = build_row(xi, deg);
        result_vec.push(row);
        assert(result_vec[idx_i].len() == deg + 1);
        assert(result_vec[idx_i][0int] == 1.0);
        if deg > 0 {
            assert(result_vec[idx_i][1int] == xi);
            assert(result_vec[idx_i][1int] == x[idx_i]);
        }
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}