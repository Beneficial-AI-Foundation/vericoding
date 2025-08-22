use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
{
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): strengthened assertion with explicit bounds check */
    assert(i == a.len() && result.len() == i);
    assert(result.len() == a.len());
    
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            result.len() == a.len() + j,
            forall|k: int| 0 <= k && k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k && k < j ==> result[k + a.len()] == b[k],
        decreases b.len() - j
    {
        result.push(b[j]);
        j += 1;
    }
    
    /* code modified by LLM (iteration 1): strengthened assertion with explicit bounds check */
    assert(j == b.len() && result.len() == a.len() + j);
    assert(result.len() == a.len() + b.len());
    
    result
}

fn main() {}
}