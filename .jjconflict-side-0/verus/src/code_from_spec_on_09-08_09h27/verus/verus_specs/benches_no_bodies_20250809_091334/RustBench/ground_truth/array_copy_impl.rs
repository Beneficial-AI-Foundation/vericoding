use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and fixed type handling */
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    
    result
}

fn main() {}
}