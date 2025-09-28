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
spec fn index_to_coords(index: usize, shape: Seq<usize>) -> Seq<usize>
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        (index as nat) < vec_product(shape),
    ensures
        result.len() == shape.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] < shape[i],
    decreases shape.len()
{
    if shape.len() == 1 {
        seq![index]
    } else {
        let stride = vec_product(shape.skip(1));
        let coord = index / stride;
        let remainder = index % stride;
        seq![coord].add(index_to_coords(remainder, shape.skip(1)))
    }
}

proof fn lemma_index_to_coords_bounds(index: usize, shape: Seq<usize>)
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        (index as nat) < vec_product(shape),
    ensures
        forall|i: int| 0 <= i < shape.len() ==> index_to_coords(index, shape)[i] < shape[i],
    decreases shape.len()
{
    if shape.len() == 1 {
    } else {
        let stride = vec_product(shape.skip(1));
        let remainder = index % stride;
        lemma_index_to_coords_bounds(remainder, shape.skip(1));
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
            (indices[i] != indices[j] ==> result[i]@ != result[j]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): declare result variable before ensures clause */
    let mut result: Vec<Vec<usize>> = Vec::new();
    let mut i = 0;
    
    while i < indices.len()
        invariant
            i <= indices.len(),
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() == shape.len(),
            forall|k: int, j: int| 0 <= k < result.len() && 0 <= j < shape.len() ==> 
                result[k][j] < shape[j],
            forall|k1: int, k2: int| 0 <= k1 < result.len() && 0 <= k2 < result.len() && k1 != k2 ==> 
                (indices[k1] != indices[k2] ==> result[k1]@ != result[k2]@),
    {
        let coords_seq = index_to_coords(indices[i], shape@);
        let mut coords = Vec::new();
        let mut j = 0;
        
        proof {
            lemma_index_to_coords_bounds(indices[i], shape@);
        }
        
        while j < shape.len()
            invariant
                j <= shape.len(),
                coords.len() == j,
                forall|k: int| 0 <= k < coords.len() ==> coords[k] == coords_seq[k],
                forall|k: int| 0 <= k < coords.len() ==> coords[k] < shape[k],
        {
            coords.push(coords_seq[j]);
            j += 1;
        }
        
        result.push(coords);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}