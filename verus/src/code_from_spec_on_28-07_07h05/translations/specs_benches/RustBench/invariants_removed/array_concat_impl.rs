use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 2): removed invalid comment text and provided proper Verus implementation */
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
{
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): added assertion to help verifier understand result.len() after first loop */
    assert(result.len() == a.len());
    
    let mut j = 0;
    /* code modified by LLM (iteration 2): added assertion to establish loop invariant before second loop */
    assert(result.len() == a.len() + j); // j is 0 here
    while j < b.len()
        invariant
            result.len() == a.len() + j,
            forall|k: int| 0 <= k && k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k && k < j ==> result[k + a.len()] == b[k],
        decreases b.len() - j
    {
        result.push(b[j]);
        j += 1;
    }
    
    /* code modified by LLM (iteration 2): added assertion to help verifier prove final postcondition */
    assert(result.len() == a.len() + b.len());
    
    result
}

fn main() {}
}