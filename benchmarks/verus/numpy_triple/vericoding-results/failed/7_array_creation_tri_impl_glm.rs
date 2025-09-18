// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): replaced cast-based condition with safe arithmetic to avoid overflow */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    for i in 0..n
        invariant
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx].len() == m,
            forall|idx: int, j: int| 0 <= idx < i && 0 <= j < m ==> 
                result[idx][j] == if j <= idx + k { 1.0 } else { 0.0 }
    {
        let mut row = Vec::new();
        for j in 0..m
            invariant
                row.len() == j,
                forall|j_idx: int| 0 <= j_idx < j ==> 
                    row[j_idx] == if j_idx <= i + k { 1.0 } else { 0.0 }
        {
            let value = if k >= 0 {
                if j <= i {
                    1.0
                } else {
                    let diff = j - i;
                    if diff <= (k as usize) {
                        1.0
                    } else {
                        0.0
                    }
                }
            } else {
                let abs_k = (-k) as usize;
                if i < abs_k {
                    0.0
                } else {
                    if j <= i - abs_k {
                        1.0
                    } else {
                        0.0
                    }
                }
            };
            row.push(value);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}