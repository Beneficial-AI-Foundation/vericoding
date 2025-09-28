// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No helpers needed.] */
// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Changed loop range type from `int` to `usize` for `for` loops in proof block to resolve compilation error.] */
{
    let n: usize = c.len();

    if n < 2 {
        // This case should not be reached due to the `c@.len() >= 2` precondition.
        // However, including a graceful handling or a panic is good practice for robustness.
        // For verification, we can rely on the precondition.
        panic!("Input vector c must have a length of at least 2");
    }

    let mut mat: Vec<Vec<f32>> = Vec::new();
    let dim: usize = n - 1; // The dimension of the companion matrix

    if n == 2 {
        // Special case for n=2, as per numpy.polynomial.chebyshev.chebcompanion
        let mut row = Vec::with_capacity(dim);
        row.push(-c[1] / (2.0 * c[0]));
        mat.push(row);
    } else {
        // Construct the companion matrix for n > 2
        // First row
        let mut first_row: Vec<f32> = Vec::with_capacity(dim);
        first_row.push(-c[n - 1] / (2.0 * c[n - 2]));
        for _ in 1..dim {
            first_row.push(0.0);
        }
        mat.push(first_row);

        // Subsequent rows
        for i in 1..dim {
            let mut row: Vec<f32> = Vec::with_capacity(dim);
            for j in 0..dim {
                if i - 1 == j {
                    row.push(0.5);
                } else {
                    row.push(0.0);
                }
            }
            mat.push(row);
        }
    }

    proof {
        // Assertions to satisfy the ensures clause
        assert(mat@.len() == (n - 1) as int);

        // This loop verifies that each inner vector has the correct length.
        // Since we explicitly `with_capacity` and then `push` elements based on `dim`,
        // the lengths should be correct.
        for i in 0..mat@.len() {
            assert((mat@[i]@.len() as int) == (n - 1) as int);
        }
    }

    mat
}
// </vc-code>

}
fn main() {}