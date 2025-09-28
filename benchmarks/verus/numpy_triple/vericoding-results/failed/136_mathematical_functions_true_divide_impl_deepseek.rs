// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_vector_len_equality<T>(v1: Vec<T>, v2: Vec<T>)
    requires
        v1.len() == v2.len(),
    ensures
        v1.len() == v2.len(),
{
    /* helper modified by LLM (iteration 5): Added missing lemma for vector length equality */
}

proof fn lemma_vector_index_in_range<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        i < v.len(),
{
    /* helper modified by LLM (iteration 5): Added missing lemma for vector index validation */
}

proof fn lemma_nonzero_division_valid(a: f64, b: f64)
    requires
        b != 0.0,
    ensures
        (#[trigger] (a / b)) is f64,
{
    /* helper modified by LLM (iteration 5): Fixed spec_euclidean_div error by using proper division syntax */
}
// </vc-helpers>

// <vc-spec>
fn true_divide(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2@[i] != 0.0,
    ensures
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed missing lemma function calls */
    let mut result = Vec::new();
    let n = x1.len();
    
    proof {
        lemma_vector_len_equality(x1, x2);
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j as int] / x2@[j as int],
    {
        proof {
            lemma_vector_index_in_range(x1, i as int);
            lemma_vector_index_in_range(x2, i as int);
            lemma_nonzero_division_valid(x1@[i as int], x2@[i as int]);
        }
        
        let quotient = x1[i] / x2[i];
        result.push(quotient);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}