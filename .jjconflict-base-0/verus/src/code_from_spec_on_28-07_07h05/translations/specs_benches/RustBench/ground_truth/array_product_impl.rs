use vstd::prelude::*;

verus! {

//IMPL array_product
#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added stronger invariant to ensure i <= a.len() and proper postcondition proof */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j && j < i ==> result[j] == (a[j] as i64) * (b[j] as i64),
        decreases a.len() - i,
    {
        let product = (a[i] as i64) * (b[i] as i64);
        result.push(product);
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition */
    assert(i == a.len());
    assert(result.len() == i);
    
    result
}

fn main() {}
}