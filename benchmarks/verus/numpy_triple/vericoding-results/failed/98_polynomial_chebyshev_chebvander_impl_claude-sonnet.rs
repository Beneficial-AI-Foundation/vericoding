// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed proof function syntax with proper body */
spec fn chebyshev_poly(n: nat, x: f32) -> f32
    decreases n
{
    if n == 0 {
        1.0f32
    } else if n == 1 {
        x
    } else {
        2.0f32 * x * chebyshev_poly((n - 1) as nat, x) - chebyshev_poly((n - 2) as nat, x)
    }
}

proof fn chebyshev_base_cases(x: f32)
    ensures chebyshev_poly(0, x) == 1.0f32
    ensures chebyshev_poly(1, x) == x
{
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
/* code modified by LLM (iteration 5): Fixed implementation */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg + 1),
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j < i ==> result[j][1] == x[j]
    {
        let mut row: Vec<f32> = Vec::new();
        
        for k in 0..(deg + 1)
            invariant
                row.len() == k,
                k >= 1 ==> row[0] == 1.0f32,
                k >= 2 && deg >= 1 ==> row[1] == x[i]
        {
            if k == 0 {
                row.push(1.0f32);
            } else if k == 1 {
                row.push(x[i]);
            } else {
                let val = 2.0f32 * x[i] * row[k-1] - row[k-2];
                row.push(val);
            }
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}