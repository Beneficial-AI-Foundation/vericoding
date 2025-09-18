// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma parameter type to match expectations */
proof fn range_inclusive_ghost_iter_lemma(lower: usize, upper: usize)
    requires lower <= upper + 1,
    decreases if upper >= lower { upper - lower + 1 } else { 0 }
{
    if lower <= upper {
        range_inclusive_ghost_iter_lemma(lower, upper - 1);
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
{
    /* code modified by LLM (iteration 5): Fixed type conversion and lemma call */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let n = x.len();
    
    let mut i: usize = 0;
    while i < n {
        let mut row: Vec<f32> = Vec::new();
        row.push(1.0f32);
        
        if deg >= 1 {
            row.push(x[i]);
            
            if deg >= 2 {
                range_inclusive_ghost_iter_lemma(2, deg);
                
                let mut j: usize = 2;
                while j <= deg {
                    let prev1 = row[j - 1];
                    let prev2 = row[j - 2];
                    let t_j = 2.0f32 * x[i] * prev1 - prev2;
                    row.push(t_j);
                    j += 1;
                }
            }
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}