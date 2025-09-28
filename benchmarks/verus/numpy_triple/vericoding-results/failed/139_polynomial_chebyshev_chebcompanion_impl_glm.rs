// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): handle division by zero and index bounds */
{
    let n = c.len();
    assert(n >= 2);
    let denom = 2.0 * c[0];
    let n_minus_one = n - 1;
    let mut result = Vec::with_capacity(n_minus_one);

    if denom == 0.0 {
        for i in 0..n_minus_one {
            let mut row = Vec::with_capacity(n_minus_one);
            for j in 0..n_minus_one {
                row.push(0.0);
            }
            result.push(row);
        }
    } else {
        for i in 0..n_minus_one {
            let mut row = Vec::with_capacity(n_minus_one);
            for j in 0..n_minus_one {
                if i == j {
                    if i == 0 {
                        row.push(c[1] / denom);
                    } else if i == n_minus_one - 1 {
                        row.push(c[n_minus_one] / denom);
                    } else {
                        row.push(0.0);
                    }
                } else if i == j + 1 || j == i + 1 {
                    row.push(1.0 / denom);
                } else {
                    row.push(0.0);
                }
            }
            result.push(row);
        }
    }

    result
}
// </vc-code>

}
fn main() {}