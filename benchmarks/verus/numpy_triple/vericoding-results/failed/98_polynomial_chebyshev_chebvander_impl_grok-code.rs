// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing inclusive range with exclusive range in for loop. */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let n = x.len();
    for i in 0..n {
        let mut row: Vec<f32> = Vec::new();
        row.push(1.0f32);
        if deg >= 1 {
            row.push(x[i]);
        }
        if deg >= 2 {
            let mut t_prev2 = 1.0f32;
            let mut t_prev = x[i];
            for k in 2..(deg + 1) {
                let t_curr = 2.0f32 * x[i] * t_prev - t_prev2;
                row.push(t_curr);
                t_prev2 = t_prev;
                t_prev = t_curr;
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}