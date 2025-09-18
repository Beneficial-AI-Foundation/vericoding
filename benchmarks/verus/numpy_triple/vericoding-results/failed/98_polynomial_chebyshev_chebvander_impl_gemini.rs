// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Unchanged from previous iteration. */
#[verifier::opaque]
fn chebyshev_step(x: f32, prev: f32, prev2: f32) -> (res: f32) {
    2.0f32 * x * prev - prev2
}
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
    /* code modified by LLM (iteration 5): Fixed compilation error by removing invalid `#![auto]` attribute. */
    let mut mat: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            mat.len() == i,
            forall|k: int| 0 <= k < i ==> mat[k].len() == deg + 1,
            forall|k: int| 0 <= k < i ==> mat[k][0] == 1.0f32,
            deg >= 1 ==> forall|k: int| 0 <= k < i ==> mat[k][1] == x[k],
        decreases x.len() - i
    {
        let x_val = x[i];
        let mut row: Vec<f32> = Vec::new();

        row.push(1.0f32);

        if deg >= 1 {
            row.push(x_val);

            let mut k: usize = 2;
            while k <= deg
                invariant
                    2 <= k <= deg + 1,
                    row.len() == k,
                    row[0] == 1.0f32,
                    row[1] == x_val,
                decreases deg + 1 - k
            {
                let t_k = chebyshev_step(x_val, row[k - 1], row[k - 2]);
                row.push(t_k);
                k = k + 1;
            }
        }

        assert(row.len() == deg + 1);
        mat.push(row);
        i = i + 1;
    }
    mat
}
// </vc-code>

}
fn main() {}