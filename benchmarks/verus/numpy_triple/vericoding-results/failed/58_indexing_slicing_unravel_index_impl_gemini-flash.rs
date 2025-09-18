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
/* helper modified by LLM (iteration 5): Removed unnecessary 'whenever' clause as it's not a Verus keyword for `ensures` */
proof fn dim_suffix_is_positive(s: Seq<usize>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] > 0,
    ensures
        (s.len() > 0 ==> vec_product(s) > 0)
{
    if s.len() > 0 {
        // TODO: add a lemma here
        // lemma_vec_product_non_zero_for_positive_dims(s);
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
/* code modified by LLM (iteration 5): Added `calculate_coords` helper function, fixed the loop invariant type error, and addressed the overall logic. */
{
    let mut result_vec = Vec::<Vec<usize>>::with_capacity(indices.len() as usize);

    for i in 0..indices.len()
        invariant
            result_vec.len() == i,
            result_vec.capacity() == indices.len() as usize,
            indices.len() == (@indices).len(),
            shape.len() > 0,
            forall|k: int| 0 <= k < shape.len() ==> shape[k] > 0,
            forall|k: int| 0 <= k < indices.len() ==> (indices[k] as nat) < vec_product(shape@),
            forall|idx: int| 0 <= idx < i ==> 
                result_vec.index(idx)@.len() == (@shape).len(),
            forall|idx: int, j: int| 0 <= idx < i && 0 <= j < (@shape).len() ==> 
                result_vec.index(idx)@[j] < (@shape)[j]
    {
        let flat_index = indices[i] as nat;
        // Apply the spec function to get the coordinates
        let coords_seq = calculate_coords(flat_index, shape@);

        proof {
            assert(coords_seq.len() == shape.len());
            assert(forall|j: int| 0 <= j < shape.len() ==> (coords_seq[j] as nat) < shape[j] as nat);
        }

        let mut current_coords = Vec::<usize>::new();
        for j in 0..shape.len()
            invariant
                current_coords.len() == j,
                current_coords.capacity() == j,
                coords_seq.len() == shape.len(),
                forall|k: int| 0 <= k < shape.len() ==> (coords_seq[k] as nat) < shape[k] as nat,
                forall|k: int| 0 <= k < j ==> current_coords.index(k) == coords_seq[k] as usize
        {
            current_coords.push(coords_seq[j]);
        }
        result_vec.push(current_coords);
    }
    result_vec
}

spec fn calculate_coords(flat_index: nat, shape: Seq<usize>) -> Seq<usize>
    decreases shape.len()
{
    if shape.len() == 0 {
        Seq::<usize>::empty()
    } else {
        let last_dim = shape.last().unwrap();
        let remaining_shape = shape.drop_last();
        let num_elements_in_prev_dims = vec_product(remaining_shape);

        let current_coord = (flat_index / num_elements_in_prev_dims) as usize;
        let remaining_index = flat_index % num_elements_in_prev_dims;

        let mut result = calculate_coords(remaining_index, remaining_shape);
        result.push(current_coord)
    }
}
// </vc-code>

}
fn main() {}