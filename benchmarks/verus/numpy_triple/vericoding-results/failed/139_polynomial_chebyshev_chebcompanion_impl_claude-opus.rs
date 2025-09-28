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
{
    /* code modified by LLM (iteration 5): Fixed array bounds checks by adding assertions about n and j relationship */
    let n = c.len() - 1;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == c@.len() - 1,
            c@.len() >= 2,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j].len() == n,
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                n == c@.len() - 1,
                c@.len() >= 2,
                row@.len() == j as int,
            decreases n - j
        {
            proof {
                assert(j < n);
                assert(n >= 1);
                assert(n - 1 - j < n);
                assert(n < c@.len());
            }
            let val = if i == 0 {
                if j == n - 1 {
                    -c[n - 1 - j] / c[n]
                } else {
                    0.0
                }
            } else if i == n - 1 {
                if j == 0 {
                    0.5
                } else if j == n - 1 {
                    -c[n - 1 - j] / (2.0 * c[n])
                } else {
                    0.0
                }
            } else {
                if j == i - 1 {
                    0.5
                } else if j == i + 1 {
                    0.5
                } else if j == n - 1 {
                    -c[n - 1 - j] / (2.0 * c[n])
                } else {
                    0.0
                }
            };
            row.push(val);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}