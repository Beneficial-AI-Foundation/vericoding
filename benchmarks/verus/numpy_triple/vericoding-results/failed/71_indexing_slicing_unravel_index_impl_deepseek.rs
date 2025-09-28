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
/* helper modified by LLM (iteration 5): Fixed nat conversion using ghost variable */
spec fn unravel_index_helper(shape: Seq<usize>, idx: nat) -> (result: Seq<usize>)
    decreases shape.len()
{
    if shape.len() == 0 {
        Seq::empty()
    } else {
        let stride = vec_product(shape.skip(1));
        let coord = idx / stride;
        let remaining = idx % stride;
        let inner = unravel_index_helper(shape.skip(1), remaining);
        inner.insert(0, coord as usize)
    }
}

proof fn unravel_index_helper_correct(shape: Seq<usize>, idx: nat)
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        idx < vec_product(shape)
    ensures
        unravel_index_helper(shape, idx)@.len() == shape.len(),
        forall|j: int| 0 <= j < shape.len() ==> unravel_index_helper(shape, idx)@[j] < shape[j],
        exists|unique_index: nat| unique_index == idx
    decreases shape.len()
{
    if shape.len() > 0 {
        let stride = vec_product(shape.skip(1));
        let coord = idx / stride;
        let remaining = idx % stride;
        assert(coord < shape[0] as nat) by {
            assert(idx < vec_product(shape));
            assert(vec_product(shape) == (shape[0] as nat) * stride);
            assert(0 <= coord < shape[0] as nat);
        }
        assert(remaining < stride);
        unravel_index_helper_correct(shape.skip(1), remaining);
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
    /* code modified by LLM (iteration 5): Fixed nat conversion using ghost variable */
    let mut result: Vec<Vec<usize>> = Vec::with_capacity(indices.len());
    let shape_seq = shape@;
    let mut i: usize = 0;
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k as usize].len() == shape.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < shape.len() ==> 
                #[trigger] result[k as usize][j] < shape[j],
            forall|k: int, m: int| 0 <= k < i && 0 <= m < i && k != m ==> 
                (indices[k as usize] != indices[m as usize] ==> result[k as usize]@ != result[m as usize]@)
        decreases indices.len() - i
    {
        ghost {
            let idx_nat: nat = indices[i] as nat;
            let coords = unravel_index_helper(shape_seq, idx_nat);
            let mut vec_coords: Vec<usize> = Vec::with_capacity(shape.len());
            let mut j: usize = 0;
            while j < coords@.len()
                invariant
                    0 <= j <= shape.len(),
                    vec_coords.len() == j,
                    forall|k: int| 0 <= k < j ==> vec_coords[k as usize] == coords@[k]
                decreases shape.len() - j
            {
                vec_coords.push(coords[j]);
                j += 1;
            }
            result.push(vec_coords);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}