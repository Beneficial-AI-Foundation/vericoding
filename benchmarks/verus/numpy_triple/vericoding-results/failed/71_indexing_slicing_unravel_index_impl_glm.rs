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
spec fn unravel_single_index_spec(idx: nat, shape: Seq<usize>) -> Seq<usize>
    decreases shape.len()
{
    if shape.len() == 0 {
        Seq::empty()
    } else {
        let product_rest = vec_product(shape.skip(1));
        let first = idx / product_rest;
        let rest = unravel_single_index_spec(idx % product_rest, shape.skip(1));
        Seq::new(shape.len(), |i: int| if i == 0 { first } else { rest[i-1] })
    }
}

/* helper modified by LLM (iteration 4): changed lemma to use #[verifier::lemma] attribute to fix compilation error */
#[verifier::lemma]
fn unravel_single_index_spec_injective(shape: Seq<usize>) -> ()
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
    ensures
        forall|i: nat, j: nat| 
            i < vec_product(shape) && j < vec_product(shape) && i != j ==> 
            unravel_single_index_spec(i, shape) != unravel_single_index_spec(j, shape)
{
    if shape.len() == 1 {
        assert forall|i: nat, j: nat| 
            #![trigger unravel_single_index_spec(i, shape)]
            #![trigger unravel_single_index_spec(j, shape)]
            i < vec_product(shape) && j < vec_product(shape) && i != j 
            implies unravel_single_index_spec(i, shape) != unravel_single_index_spec(j, shape)
        {
            assert(i != j);
        }
    } else {
        let product_rest = vec_product(shape.skip(1));
        assert forall|i: nat, j: nat| 
            #![trigger unravel_single_index_spec(i, shape)]
            #![trigger unravel_single_index_spec(j, shape)]
            i < vec_product(shape) && j < vec_product(shape) && i != j 
            implies unravel_single_index_spec(i, shape) != unravel_single_index_spec(j, shape)
        {
            let first_i = i / product_rest;
            let rest_i = i % product_rest;
            let first_j = j / product_rest;
            let rest_j = j % product_rest;
            if first_i != first_j {
                assert(unravel_single_index_spec(i, shape) != unravel_single_index_spec(j, shape));
            } else {
                assert(rest_i != rest_j);
                unravel_single_index_spec_injective(shape.skip(1));
                assert(unravel_single_index_spec(rest_i, shape.skip(1)) != unravel_single_index_spec(rest_j, shape.skip(1)));
            }
        }
    }
}

fn unravel_single_index_exec(idx: usize, shape: &Vec<usize>) -> (res: Vec<usize>)
    requires
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        (idx as nat) < vec_product(shape@),
    ensures
        res.len() == shape.len(),
        forall|i: int| 0 <= i < res.len() ==> res[i] < shape[i],
        res@ == unravel_single_index_spec(idx as nat, shape@)
{
    if shape.len() == 1 {
        vec![idx]
    } else {
        let product_rest = vec_product(shape@[1..]);
        let first = (idx as nat) / product_rest;
        let rest_idx = (idx as nat) % product_rest;
        let rest = unravel_single_index_exec(rest_idx as usize, &shape[1..]);
        let mut res = Vec::new();
        res.push(first as usize);
        res.extend(rest);
        res
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
/* code modified by LLM (iteration 4): updated to use fixed lemma */
{
    let mut result = Vec::new();
    for i in 0..indices.len() {
        let unraveled = unravel_single_index_exec(indices[i], &shape);
        result.push(unraveled);
    }
    proof {
        unravel_single_index_spec_injective(shape@);
        assert forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result.len() && i != j && indices[i] != indices[j]
            implies result[i]@ != result[j]@
        {
            // By the ensures of unravel_single_index_exec, we have:
            //   result[i]@ = unravel_single_index_spec(indices[i] as nat, shape@)
            //   result[j]@ = unravel_single_index_spec(indices[j] as nat, shape@)
            // And by the lemma, since indices[i] != indices[j], then the spec unravelings are different.
        }
    }
    result
}
// </vc-code>

}
fn main() {}