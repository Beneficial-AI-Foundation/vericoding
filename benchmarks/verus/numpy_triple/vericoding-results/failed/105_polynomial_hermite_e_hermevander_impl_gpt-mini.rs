// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): nonnegative predicate for deg */ spec fn deg_nonneg(d: int) -> bool { d >= 0 }
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
    /* code modified by LLM (iteration 5): build Hermite-style Vandermonde rows (powers) with proper loop invariants */
    let m = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant result.len() == i,
        decreases m - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j <= deg
            invariant row.len() == j,
            decreases (deg + 1) - j
        {
            if j == 0 {
                row.push(1.0);
            } else {
                let prev = row@[row.len() - 1];
                row.push(prev * x@[i]);
            }
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