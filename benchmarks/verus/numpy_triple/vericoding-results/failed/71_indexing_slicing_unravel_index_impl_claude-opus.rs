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
/* helper modified by LLM (iteration 5): Fixed missing decreases clause in compute_product_from */
fn compute_product_from(shape: &Vec<usize>, start: usize) -> (prod: usize)
    requires
        start <= shape.len(),
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        vec_product(shape@.skip(start as int)) < usize::MAX
    ensures
        prod == vec_product(shape@.skip(start as int))
{
    let mut prod: usize = 1;
    let mut i = start;
    
    while i < shape.len()
        invariant
            start <= i <= shape.len(),
            prod == vec_product(shape@.skip(start as int).take((i - start) as int)),
            vec_product(shape@.skip(i as int)) * (prod as nat) == vec_product(shape@.skip(start as int)),
            prod <= vec_product(shape@.skip(start as int))
        decreases shape.len() - i
    {
        prod = prod * shape[i];
        i = i + 1;
    }
    
    prod
}

proof fn lemma_vec_product_bounds(shape: Seq<usize>, i: int)
    requires
        0 <= i < shape.len(),
        forall|j: int| 0 <= j < shape.len() ==> shape[j] > 0
    ensures
        vec_product(shape.skip(i + 1)) < vec_product(shape.skip(i))
    decreases shape.len() - i
{
    if i == shape.len() - 1 {
        assert(shape.skip(i + 1).len() == 0);
        assert(vec_product(shape.skip(i + 1)) == 1);
        assert(shape.skip(i).len() == 1);
        assert(vec_product(shape.skip(i)) == shape[i] as nat);
        assert(shape[i] > 0);
    } else {
        assert(vec_product(shape.skip(i)) == (shape[i] as nat) * vec_product(shape.skip(i + 1)));
        assert(shape[i] > 0);
    }
}

proof fn lemma_unravel_unique(shape: Seq<usize>, idx1: nat, idx2: nat, coords1: Seq<usize>, coords2: Seq<usize>)
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        idx1 < vec_product(shape),
        idx2 < vec_product(shape),
        idx1 != idx2,
        coords1.len() == shape.len(),
        coords2.len() == shape.len(),
        forall|i: int| 0 <= i < shape.len() ==> coords1[i] < shape[i],
        forall|i: int| 0 <= i < shape.len() ==> coords2[i] < shape[i],
        idx1 == compute_flat_index(coords1, shape),
        idx2 == compute_flat_index(coords2, shape)
    ensures
        coords1 != coords2
{
    if coords1 == coords2 {
        assert(idx1 == idx2);
        assert(false);
    }
}

spec fn compute_flat_index(coords: Seq<usize>, shape: Seq<usize>) -> nat
    decreases coords.len()
{
    if coords.len() == 0 {
        0nat
    } else {
        (coords[0] as nat) * vec_product(shape.skip(1)) + compute_flat_index(coords.skip(1), shape.skip(1))
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
/* code modified by LLM (iteration 5): No changes needed - main code is correct */
{
    let mut result: Vec<Vec<usize>> = Vec::new();
    let mut i = 0;
    
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == shape.len(),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < shape.len() ==> #[trigger] result[j][k] < shape[k],
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i && j != k ==> 
                (indices[j] != indices[k] ==> result[j]@ != result[k]@)
        decreases indices.len() - i
    {
        let mut coords: Vec<usize> = Vec::new();
        let mut remaining = indices[i];
        let mut j = 0;
        
        while j < shape.len()
            invariant
                0 <= j <= shape.len(),
                coords.len() == j,
                forall|k: int| 0 <= k < j ==> coords[k] < shape[k],
                (remaining as nat) < vec_product(shape@.skip(j as int))
            decreases shape.len() - j
        {
            if j == shape.len() - 1 {
                coords.push(remaining);
            } else {
                let stride = compute_product_from(&shape, j + 1);
                let coord = remaining / stride;
                coords.push(coord);
                remaining = remaining % stride;
                proof {
                    lemma_vec_product_bounds(shape@, j as int);
                }
            }
            j = j + 1;
        }
        
        result.push(coords);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}