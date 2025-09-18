// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error with usize to f32 cast by properly converting usize to f32 via int */
fn hermpoly(n: usize, x: f32) -> f32
    decreases n
{
    if n == 0 {
        1.0f32
    } else if n == 1 {
        2.0f32 * x
    } else {
        let hn1 = hermpoly(n-1, x);
        let hn2 = hermpoly(n-2, x);
        2.0f32 * x * hn1 - 2.0f32 * ((n-1) as int as f32) * hn2
    }
}
// </vc-helpers>

// <vc-spec>
fn hermegrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> (
            (c.len() == 0 || (exists|k: int| 0 <= k < c.len() && c[k].len() == 0) ==> result[i][j] == 0.0f32)
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented the actual grid evaluation using Hermite polynomials instead of assume */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        decreases x.len() - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        while j < y.len()
            decreases y.len() - j
        {
            let mut val = 0.0f32;
            let mut k = 0;
            while k < c.len()
                decreases c.len() - k
            {
                let c_k = &c[k];
                let mut l = 0;
                while l < c_k.len()
                    decreases c_k.len() - l
                {
                    val = val + c_k[l] * hermpoly(k, x[i]) * hermpoly(l, y[j]);
                    l = l + 1;
                }
                k = k + 1;
            }
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