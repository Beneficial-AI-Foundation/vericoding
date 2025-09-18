// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): None needed */
// </vc-helpers>

// <vc-spec>
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed invalid #![auto] attribute from assert forall statements to fix compilation error */
{
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(n);
    let kk: i64 = #[verifier::truncate] (k as i64);
    for i in 0..n {
        let mut row: Vec<f64> = Vec::with_capacity(m);
        let ii: i64 = #[verifier::truncate] (i as i64);
        for j in 0..m {
            let jj: i64 = #[verifier::truncate] (j as i64);
            let add: i64 = #[verifier::truncate] (ii + kk);
            let val = if jj <= add { 1.0 } else { 0.0 };
            row.push(val);
        }
        result.push(row);
    }
    proof {
        assert(result.len() == n);
        assert forall |i| 0 <= i < result.len() ==> result@[i].len() == m ;
        assert forall |i, j| 0 <= i < result.len() && 0 <= j < result@[i].len() ==> result@[i]@[j] == if (j as int) <= (i as int) + (k as int) { 1.0 } else { 0.0 } ;
    }
    result
}
// </vc-code>

}
fn main() {}