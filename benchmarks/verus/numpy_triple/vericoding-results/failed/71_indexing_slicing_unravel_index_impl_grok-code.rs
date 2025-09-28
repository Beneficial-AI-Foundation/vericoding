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
spec fn ravel_index(unraveled: Seq<usize>, shape: Seq<usize>) -> nat
    requires
        unraveled.len() == shape.len(),
        forall|j: int| 0 <= j < shape.len() ==> unraveled[j] < shape[j]
    decreases shape.len()
{
    if shape.len() == 0 {
        0nat
    } else {
        unraveled[0] as nat * vec_product(shape.skip(1)) + ravel_index(unraveled.skip(1), shape.skip(1))
    }
}

proof fn lemma_a_times_x_ne_b_times_x(a: nat, b: nat, x: int)
    requires
        a != b,
        x > 0
    ensures
        (a * x) as nat != (b * x) as nat
{}

proof fn lemma_ravel_injective(a: Seq<usize>, b: Seq<usize>, shape: Seq<usize>)
    requires
        a.len() == shape.len(),
        forall|j: int| 0 <= j < shape.len() ==> a[j] < shape[j],
        b.len() == shape.len(),
        forall|j: int| 0 <= j < shape.len() ==> b[j] < shape[j],
        a != b
    ensures
        ravel_index(a, shape) != ravel_index(b, shape)
    decreases shape.len()
{
    if shape.len() == 0 {
        // Equal by contradiction
    } else {
        if a[0] != b[0] {
            lemma_a_times_x_ne_b_times_x(a[0] as nat, b[0] as nat, vec_product(shape.skip(1)) as int);
        } else {
            lemma_ravel_injective(a.skip(1), b.skip(1), shape.skip(1));
        }
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
    /* code modified by LLM (iteration 5): changed variable types to usize for executable code to fix compilation errors */
    let mut result: Vec<Vec<usize>> = Vec::new();
    let num_indices = indices.len();
    let mut i: usize = 0;
    while i < num_indices
        invariant
            i <= num_indices,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == shape.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < shape.len() ==> #[trigger] result[k][j] < shape[j],
        decreases num_indices - i
    {
        let mut curr: usize = indices[i];
        let mut unravel: Vec<usize> = Vec::new();
        let mut j: usize = shape.len();
        while j > 0
            invariant
                j <= shape.len(),
                unravel.len() == shape.len() - j,
                curr >= 0,
                forall|p: int| 0 <= p < j ==> unravel[p] < shape[p] && (p + shape.len() - j) < shape.len(),
            decreases j
        {
            j -= 1;
            let dim_size = shape[j];
            unravel.push(curr % dim_size);
            curr = curr / dim_size;
        }
        proof {
            assert(ravel_index(unravel@, shape@) == indices[i] as nat);
            assert(forall|k: int, l: int| 0 <= k < unravel.len() && 0 <= l < unravel.len() && k != l ==> indices[i] != indices[l] ==> unravel@ != result[l]@);
        }
        result.push(unravel);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}