// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive float power with usize exponent */
fn f32_pow(base: f32, exp: usize) -> f32
    decreases
        exp
{
    if exp == 0 {
        1.0f32
    } else {
        base * f32_pow(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn polyvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build Vandermonde matrix using usize indices and f32_pow */
    let n = x.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|r: int| 0 <= r < (i as int) ==> result[r as usize].len() == deg + 1,
            forall|r: int| 0 <= r < (i as int) ==> result[r as usize][0] == 1.0f32,
            (deg > 0) ==> forall|r: int| 0 <= r < (i as int) ==> result[r as usize][1] == x[r as usize],
        decreases
            n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < deg + 1
            invariant
                j <= deg + 1,
                row.len() == j,
                forall|k: int| 0 <= k < (j as int) ==> (if k == 0 { row[k as usize] == 1.0f32 } else { row[k as usize] == f32_pow(x[i], k as usize) }),
            decreases
                (deg + 1) - j
        {
            if j == 0 {
                row.push(1.0f32);
            } else {
                let p = f32_pow(x[i], j);
                row.push(p);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}