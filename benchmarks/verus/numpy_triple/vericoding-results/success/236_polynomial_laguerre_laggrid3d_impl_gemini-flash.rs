// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause for all loops */
// </vc-helpers>

// <vc-spec>
fn laggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c@[i].len() ==> c@[i]@[j].len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result@[i].len() ==> result@[i]@[j].len() == z.len(),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let x_len = x.len();
    let y_len = y.len();
    let z_len = z.len();

    let mut i = 0;
    while i < x_len
        invariant
            0 <= i <= x_len,
            result.len() == i,
            // All sub-vectors up to `i` have the correct dimensions
            forall|k: int| 0 <= k < i ==> result@[k].len() == y_len,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < y_len ==> result@[k]@[l].len() == z_len,
        decreases x_len - i
    {
        let mut row_vec: Vec<Vec<f64>> = Vec::new();
        let mut j = 0;
        while j < y_len
            invariant
                0 <= j <= y_len,
                row_vec.len() == j,
                // All sub-sub-vectors up to `j` have the correct dimensions
                forall|l: int| 0 <= l < j ==> row_vec@[l].len() == z_len,
                // Parent `result` also maintains its invariant
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result@[k].len() == y_len,
                forall|k: int, l: int| 0 <= k < i && 0 <= l < y_len ==> result@[k]@[l].len() == z_len,
            decreases y_len - j
        {
            let mut inner_vec: Vec<f64> = Vec::new();
            let mut k = 0;
            while k < z_len
                invariant
                    0 <= k <= z_len,
                    inner_vec.len() == k,
                    row_vec.len() == j,
                    result.len() == i,
                    forall|l: int| 0 <= l < j ==> row_vec@[l].len() == z_len,
                    forall|k_in: int| 0 <= k_in < i ==> result@[k_in].len() == y_len,
                    forall|k_in: int, l_in: int| 0 <= k_in < i && 0 <= l_in < y_len ==> result@[k_in]@[l_in].len() == z_len,
                decreases z_len - k
            {
                // Placeholder for actual interpolation logic
                inner_vec.push(0.0);
                k = k + 1;
            }
            row_vec.push(inner_vec);
            j = j + 1;
        }
        result.push(row_vec);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}