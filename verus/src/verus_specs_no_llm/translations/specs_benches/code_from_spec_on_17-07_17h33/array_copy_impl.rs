use vstd::prelude::*;

verus! {

//IMPL array_copy
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
            /* code modified by LLM (iteration 3): Added invariant to track that i doesn't exceed a.len() */
            i <= a.len(),
        decreases a.len() - i,
    {
        result.push(a[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): Added assertion to help prove postcondition */
    assert(i == a.len());
    assert(result.len() == i);
    
    result
}

fn main() {}
}