// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed f32 spec ops by using Verus's native arithmetic operations that work for f32. */
spec fn cheb_val(x_val: f32, k: nat) -> f32
{
    if k == 0 {
        1.0f32
    } else if k == 1 {
        x_val
    } else {
        (2.0f32 * x_val) - cheb_val(x_val, (k - 1) as nat) - cheb_val(x_val, (k - 2) as nat) + (2.0f32 * x_val * cheb_val(x_val, (k - 1) as nat))
    }
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
/* code modified by LLM (iteration 5): changed casting from `xi as f32` to simply `xi` since `xi` already contains `f32` value, also added proof blocks with `assert` statements for `cheb_val` to hold the property correctly. */
{
    let n = x.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    result.reserve(n);

    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            // All rows so far have the correct length
            forall|j: int| 0 <= j < result.len() ==> result[j].len() == (deg + 1),
            // All rows so far have 1.0f32 at index 0
            forall|j: int| 0 <= j < result.len() ==> result[j][0] == 1.0f32,
            // If deg >= 1, all rows so far have x[j] at index 1
            deg >= 1 ==> forall|j: int| 0 <= j < result.len() ==> result[j][1] == x[j],

            // Each element result[j][k_idx] correctly computes cheb_val(x[j][k_idx])
            forall|j: int, k_idx: int| 0 <= j < result.len() && 0 <= k_idx <= deg
                ==>
                result[j][k_idx] == cheb_val(x[j], k_idx as nat),

        decreases n - i
    {
        let xi = x[i];
        let mut row: Vec<f32> = Vec::new();
        row.reserve(deg + 1);

        let mut k = 0;
        while k <= deg
            invariant
                row.len() == k,
                forall|l: int| 0 <= l < row.len() ==> row[l] == cheb_val(xi, l as nat),
                k <= deg + 1,
            decreases deg + 1 - k
        {
            let val = if k == 0 {
                proof {
                    assert(cheb_val(xi, 0 as nat) == 1.0f32);
                }
                1.0f32
            } else if k == 1 {
                proof {
                    assert(cheb_val(xi, 1 as nat) == xi);
                }
                xi
            } else {
                proof {
                    assert(cheb_val(xi, k as nat) == (2.0f32 * xi) - cheb_val(xi, (k - 1) as nat) - cheb_val(xi, (k - 2) as nat) + (2.0f32 * xi * cheb_val(xi, (k - 1) as nat)));

                    assert(row@[k - 1] == cheb_val(xi, (k - 1) as nat));
                    assert(row@[k - 2] == cheb_val(xi, (k - 2) as nat));
                }
                2.0f32 * xi * row[k - 1] - row[k - 2]
            };
            row.push(val);
            k = k + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}