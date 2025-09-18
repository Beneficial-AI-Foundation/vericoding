// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn vec_product(shape: Seq<usize>) -> nat
    decreases shape.len()
{
    if shape.len() == 0 {
        1nat
    } else {
        (shape[0] as nat) * vec_product(shape.skip(1))
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unravel_index(indices: Vec<usize>, shape: Vec<usize>) -> (result: Vec<Vec<usize>>)
    requires 
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] as nat) < vec_product(shape@),
    ensures
        result.len() == indices.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == shape.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < shape.len() ==> 
            #[trigger] result[i][j] < shape[j],
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            (indices[i] != indices[j] ==> result[i] != result[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementing unravel_index with proper loop structure */
    let mut result: Vec<Vec<usize>> = Vec::new();
    let mut i: usize = 0;
    
    while i < indices.len()
        invariant
            i <= indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == shape.len(),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < shape.len() ==> 
                #[trigger] result[j][k] < shape[k],
        decreases indices.len() - i
    {
        let flat_idx = indices[i];
        let mut multi_idx: Vec<usize> = Vec::new();
        let mut remaining = flat_idx;
        let mut j: usize = 0;
        
        while j < shape.len()
            invariant
                j <= shape.len(),
                multi_idx.len() == j,
                remaining <= flat_idx,
                forall|k: int| 0 <= k < j ==> multi_idx[k] < shape[k],
            decreases shape.len() - j
        {
            if j == shape.len() - 1 {
                multi_idx.push(remaining);
            } else {
                let mut stride: usize = 1;
                let mut k = j + 1;
                
                while k < shape.len()
                    invariant
                        j + 1 <= k <= shape.len(),
                        stride >= 1,
                    decreases shape.len() - k
                {
                    stride = stride * shape[k];
                    k = k + 1;
                }
                
                let idx = remaining / stride;
                multi_idx.push(idx);
                remaining = remaining % stride;
            }
            j = j + 1;
        }
        
        result.push(multi_idx);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}