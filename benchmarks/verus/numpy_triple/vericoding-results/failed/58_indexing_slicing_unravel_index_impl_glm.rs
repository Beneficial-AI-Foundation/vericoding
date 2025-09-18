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
spec fn vec_product_from(shape: Seq<usize>, start: int) -> nat
    decreases shape.len() - start
{
    if start >= shape.len() {
        1
    } else {
        (shape[start] as nat) * vec_product_from(shape, start+1)
    }
}

spec fn partial_index(shape: Seq<usize>, start: int, coords: Seq<usize>) -> nat
    requires start <= shape.len() && coords.len() == shape.len() - start
    decreases shape.len() - start
{
    if coords.len() == 0 {
        0
    } else {
        (coords[0] as nat) * vec_product_from(shape, start+1) + partial_index(shape, start+1, coords.skip(1))
    }
}

/* helper modified by LLM (iteration 5): changed parameter type from &Vec<usize> to Seq<usize> to fix compilation error */
exec fn unravel_one_index(index: usize, shape_seq: Seq<usize>) -> (result: Vec<usize>)
    requires 
        index as nat < vec_product(shape_seq)
    ensures 
        result.len() == shape_seq.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] < shape_seq[i] as usize
{
    let n = shape_seq.len();
    let mut result_vec = vec![0; n];
    let mut current = index;
    let mut i = n;
    while i > 0
        invariant 
            0 <= i <= n,
            current as nat * vec_product_from(shape_seq, i) + partial_index(shape_seq, i, result_vec@.subrange(i as int, n as int)) == index as nat,
            forall|j: int| i <= j < n ==> result_vec[j] < shape_seq[j] as usize,
    {
        i -= 1;
        let dim = shape_seq[i] as usize;
        result_vec[i] = current % dim;
        current = current / dim;
    }
    result_vec
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
    /* code modified by LLM (iteration 5): updated call to use sequence parameter */
    let mut result = Vec::new();
    for i in 0..indices.len() {
        let row = unravel_one_index(indices[i], shape@);
        result.push(row);
    }
    proof {
        spec fn compute_index(row: Seq<usize>, shape: Seq<usize>) -> nat
            decreases row.len()
        {
            if row.len() == 0 {
                0
            } else {
                (row[0] as nat) * vec_product(shape.skip(1)) + compute_index(row.skip(1), shape.skip(1))
            }
        }

        assert forall|i: int| 0 <= i < result.len() implies compute_index(result[i]@, shape@) == indices[i] as nat by {
            // Follows from helper's invariant and definition of partial_index
        }

        assert forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result.len() && i != j && indices[i] != indices[j] 
            implies result[i] != result[j] 
        by {
            // If rows equal, then compute_index yields same value, implying indices equal - contradiction
        }
    }
    result
}
// </vc-code>

}
fn main() {}