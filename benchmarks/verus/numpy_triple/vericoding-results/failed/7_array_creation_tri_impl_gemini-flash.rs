// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this fix. */
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
/* code modified by LLM (iteration 5): Fixed syntax error in forall quantifier within proof block. */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    
    #[invariant(result.len() <= n)]
    for i in 0..n {
        let mut row: Vec<f64> = Vec::new();
        #[invariant(row.len() <= m)]
        for j in 0..m {
            let val = if (j as int) <= (i as int) + (k as int) { 1.0 } else { 0.0 };
            row.push(val);
        }
        proof {
            assert(row.len() == m as int);
        }
        result.push(row);
    }
    proof {
        assert(result.len() == n as int);
        forall |i: int| #![auto]
            0 <= i && i < n ==> result.view_nth(i).len() == m as int
        ;
        forall |i: int, j: int| #![auto]
            0 <= i && i < n && 0 <= j && j < m ==> result.view_nth(i).view_nth(j) == if (j as int) <= (i as int) + (k as int) { 1.0 } else { 0.0 }
        ;
    }
    result
}
// </vc-code>

}
fn main() {}