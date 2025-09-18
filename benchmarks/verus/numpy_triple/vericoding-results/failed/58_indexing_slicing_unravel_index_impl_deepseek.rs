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
/* helper modified by LLM (iteration 5): Fixed sequence indexing and conversion functions */
proof fn index_uniqueness_lemma(indices: Seq<usize>, results: Seq<Seq<usize>>, shape: Seq<usize>)
    requires
        indices.len() == results.len(),
        forall|i: int| 0 <= i < results.len() ==> results[i] == flatten_index(indices[i] as usize, shape),
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0
    ensures
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && i != j ==> 
            (indices[i] != indices[j] ==> results[i] != results[j])
{
}

spec fn flatten_index(index: usize, shape: Seq<usize>) -> Seq<usize>
    decreases shape.len()
{
    if shape.len() == 0 {
        seq![]
    } else {
        let remaining_dims = shape.skip(1);
        let remaining_elems = vec_product(remaining_dims);
        
        let current_idx = index / remaining_elems as usize;
        let next_index = index % remaining_elems as usize;
        
        seq![current_idx].add(flatten_index(next_index, remaining_dims))
    }
}

proof fn vec_product_positive(shape: Seq<usize>)
    requires shape.len() > 0, forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0
    ensures vec_product(shape) > 0
    decreases shape.len()
{
    if shape.len() == 1 {
        assert(shape[0] > 0);
    } else {
        vec_product_positive(shape.skip(1));
    }
}
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
/* code modified by LLM (iteration 5): Fixed sequence indexing and conversion */
{
    let mut result: Vec<Vec<usize>> = Vec::new();
    
    let mut idx = 0;
    while idx < indices.len()
        invariant
            0 <= idx <= indices.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == shape.len(),
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < shape.len() ==> 
                result[i][j] < shape[j],
            forall|i: int| 0 <= i < result.len() ==> 
                result[i]@ == flatten_index(indices[i] as usize, shape@)
    {
        let index_value = indices[idx] as usize;
        let flat_indices = flatten_index(index_value, shape@);
        let mut current_result = Vec::new();
        
        let mut k = 0;
        while k < shape.len()
            invariant
                0 <= k <= shape.len(),
                current_result.len() == k,
                forall|j: int| 0 <= j < k ==> current_result[j] == flat_indices@[j] as usize
        {
            current_result.push(flat_indices@[k] as usize);
            k += 1;
        }
        
        result.push(current_result);
        idx += 1;
    }
    
    let result_seq: Seq<Seq<usize>> = Seq::from(result.iter().map(|v| v@).collect());
    index_uniqueness_lemma(indices@, result_seq, shape@);
    result
}
// </vc-code>

}
fn main() {}