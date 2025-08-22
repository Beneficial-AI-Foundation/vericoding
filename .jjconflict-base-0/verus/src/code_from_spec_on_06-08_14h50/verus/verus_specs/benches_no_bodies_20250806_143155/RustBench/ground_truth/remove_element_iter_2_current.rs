use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    requires
        0 <= pos < a.len(),
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
{
    let mut result = Vec::new();
    
    // Copy elements before pos
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < pos
        invariant
            0 <= i <= pos,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases pos - i,
    {
        result.push(a[i]);
        i += 1;
    }
    
    // Skip element at pos and copy remaining elements
    let mut j = pos + 1;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while j < a.len()
        invariant
            pos < j <= a.len(),
            result.len() == pos + (j - pos - 1),
            forall|k: int| 0 <= k < pos ==> result[k] == a[k],
            forall|k: int| pos <= k < result.len() ==> result[k] == a[k + 1],
        decreases a.len() - j,
    {
        result.push(a[j]);
        j += 1;
    }
    
    result
}

fn main() {}
}