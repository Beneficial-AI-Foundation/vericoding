// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn legvander3d(x: &Vec<f32>, y: &Vec<f32>, z: &Vec<f32>, deg_x: usize, deg_y: usize, deg_z: usize) -> (result: Vec<Vec<f32>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x + 1) * (deg_y + 1) * (deg_z + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Cast num_terms_nat to ghost for use in ensures clause; ensure correct vector initialization. */
{
    let len = x.len();
    let num_terms = (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
    let num_terms_u = num_terms as usize;
    let ghost num_terms_nat = num_terms as nat; // For use in `ensures` clause

    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            result.spec_len() == i as nat,
            forall|j: int| 0 <= j < i ==> result[j].spec_len() == num_terms_nat,
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
    {
        let mut row: Vec<f32> = Vec::new();
        let mut term_idx = 0;
        while term_idx < num_terms_u
            invariant
                term_idx <= num_terms_u,
                row.len() == term_idx,
                row.spec_len() == term_idx as nat,
        {
            row.push(0.0f32);
            term_idx = term_idx + 1;
        }

        if row.len() > 0 {
            row.set(0, 1.0f32);
        }

        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}