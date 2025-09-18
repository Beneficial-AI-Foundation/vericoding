// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): build Chebyshev row with reserved capacity and prove postconditions */
fn chebvander_row(x: f32, deg: usize) -> (result: Vec<f32>)
    ensures result.len() == deg + 1,
            result[0] == 1.0f32,
            deg >= 1 ==> result[1] == x
{
    let n = deg + 1;
    let mut row = Vec::<f32>::with_capacity(n);
    let mut i = 0usize;
    while i < n
        invariant i <= n && row.len() == i,
        decreases n - i
    {
        if i == 0 {
            row.push(1.0f32);
        } else if i == 1 {
            row.push(x);
        } else {
            // i >= 2 => indices i-1 and i-2 are valid because row.len() == i
            let t_im1 = row[i - 1];
            let t_im2 = row[i - 2];
            row.push(2.0f32 * x * t_im1 - t_im2);
        }
        i += 1;
    }
    // Prove postconditions
    assert(row.len() == n);
    assert(n >= 1);
    assert(row[0] == 1.0f32);
    if deg >= 1 {
        assert(row[1] == x);
    }
    row
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
    /* code modified by LLM (iteration 5): build result using chebvander_row with reserved capacity and maintain invariants */
    let n = x.len();
    let mut result = Vec::<Vec<f32>>::with_capacity(n);
    let mut i = 0usize;
    while i < n
        invariant i <= n && result.len() == i,
                  n == x.len(),
                  forall|j: int| 0 <= j < i as int ==> result[j].len() == deg + 1,
                  forall|j: int| 0 <= j < i as int ==> result[j][0] == 1.0f32,
                  deg >= 1 ==> forall|j: int| 0 <= j < i as int ==> result[j][1] == x[j],
        decreases n - i
    {
        let xi = x[i];
        let row = chebvander_row(xi, deg);
        result.push(row);
        i += 1;
    }
    assert(result.len() == n);
    result
}
// </vc-code>

}
fn main() {}