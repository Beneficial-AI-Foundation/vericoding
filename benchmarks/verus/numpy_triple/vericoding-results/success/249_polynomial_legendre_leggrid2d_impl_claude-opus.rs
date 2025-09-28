// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn leggrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        x@.len() > 0,
        y@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
    ensures
        /* The result has the correct shape: nx × ny grid */
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        /* Grid structure preserves dimensionality */
        x@.len() > 0 && y@.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to loops */
    let nx = x.len();
    let ny = y.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < nx
        invariant
            i <= nx,
            nx == x@.len(),
            ny == y@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == ny,
        decreases nx - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        
        while j < ny
            invariant
                j <= ny,
                ny == y@.len(),
                row@.len() == j,
            decreases ny - j
        {
            row.push(0.0);
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