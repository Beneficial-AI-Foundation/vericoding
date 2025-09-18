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
/* helper modified by LLM (iteration 5): fixed type mismatches between nat and usize */
spec fn index_to_coordinates(index: usize, shape: Seq<usize>) -> (result: Seq<usize>)
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        (index as nat) < vec_product(shape)
    ensures
        result.len() == shape.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] < shape[i]
    decreases shape.len()
{
    if shape.len() == 1 {
        seq![index]
    } else {
        let first_dim = shape[0];
        let remaining_shape = shape.skip(1);
        let remaining_product = vec_product(remaining_shape) as usize;
        let coord = index / remaining_product;
        let remaining_index = index % remaining_product;
        seq![coord].add(index_to_coordinates(remaining_index, remaining_shape))
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
{
    /* code modified by LLM (iteration 5): fixed sequence indexing and length casting */
    let mut result: Vec<Vec<usize>> = Vec::new();
    for i in 0..indices.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() == shape.len(),
            forall|k: int, j: int| 0 <= k < result.len() && 0 <= j < shape.len() ==> 
                result[k][j] < shape[j],
            forall|k1: int, k2: int| 0 <= k1 < result.len() && 0 <= k2 < result.len() && k1 != k2 ==> 
                (indices[k1] != indices[k2] ==> result[k1] != result[k2])
    {
        let coords = index_to_coordinates(indices[i], shape@);
        let mut coord_vec = Vec::new();
        for j in 0..coords.len()
            invariant
                coord_vec.len() == j,
                coords.len() == shape.len(),
                forall|k: int| 0 <= k < coord_vec.len() ==> coord_vec[k] == coords[k],
                forall|k: int| 0 <= k < coords.len() ==> coords[k] < shape[k]
        {
            proof {
                let idx = j as int;
                assert(0 <= idx < coords.len());
                assert(coords[idx] < shape[idx]);
            }
            let ghost idx_ghost = j as int;
            let coord_val = coords[idx_ghost];
            coord_vec.push(coord_val);
        }
        result.push(coord_vec);
    }
    result
}
// </vc-code>

}
fn main() {}