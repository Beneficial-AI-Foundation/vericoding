// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert to ghost function and fix signature */
spec fn tri_helper(i: int, j: int, k: i32) -> bool
    ensures result == (j <= i + k as int)
{
    j <= i + k as int
}
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
/* code modified by LLM (iteration 5): Fix type casting from usize to int */
{
    let mut result = Vec::<Vec<f64>>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|ii: int| 0 <= ii < i ==> result[ii].len() == m,
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < m ==> 
                result[ii][jj] == if jj <= ii + k as int { 1.0 } else { 0.0 }
    {
        let mut row = Vec::<f64>::new();
        let mut j: usize = 0;
        
        while j < m
            invariant
                0 <= j <= m,
                row.len() == j,
                forall|jj: int| 0 <= jj < j ==> 
                    row[jj] == if jj <= i as int + k as int { 1.0 } else { 0.0 }
        {
            let value: f64 = if tri_helper(i as int, j as int, k) { 1.0 } else { 0.0 };
            row.push(value);
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