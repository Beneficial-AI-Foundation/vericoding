// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn tril(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            #[trigger] result[i][j] == if i >= j - k { m[i][j] } else { 0.0 },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The verification errors regarding 'nat' and 'int' types in `if r_idx as int >= c_idx as int - k as int` mean that these types, when used in direct comparisons, are considered ghost types. To fix this, I have explicitly cast `r_idx`, `c_idx`, and `k` to their concrete types (`usize` and `i32` respectively) before converting them to `int` for the comparison, ensuring Verus considers them during verification.*/
    let mut result: Vec<Vec<f64>> = Vec::new();
    let rows = m.len();
    let cols = m[0].len();

    let mut r_idx = 0;
    while r_idx < rows
        invariant
            result.len() == r_idx,
            r_idx <= rows,
            forall|i: int| 0 <= i < r_idx ==> #[trigger] result[i].len() == cols,
            forall|i: int, j: int|
                0 <= i < r_idx && 0 <= j < cols ==> #[trigger] result[i][j] == (if i >= j - k { m[i as usize][j as usize] } else { 0.0 }),
    {
        let mut row_vec: Vec<f64> = Vec::new();
        let mut c_idx = 0;
        while c_idx < cols
            invariant
                row_vec.len() == c_idx,
                c_idx <= cols,
                forall|j: int| 0 <= j < c_idx ==> #[trigger] row_vec[j] == (if r_idx as int >= j - k { m[r_idx as usize][j as usize] } else { 0.0 }),
        {
            if (r_idx as i32) >= (c_idx as i32) - k {
                row_vec.push(m[r_idx][c_idx]);
            } else {
                row_vec.push(0.0);
            }
            c_idx = c_idx + 1;
        }
        result.push(row_vec);
        r_idx = r_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}