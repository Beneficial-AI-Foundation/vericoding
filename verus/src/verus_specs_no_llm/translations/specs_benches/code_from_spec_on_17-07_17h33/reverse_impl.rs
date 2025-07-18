use vstd::prelude::*;

verus! {

fn reverse(a: &[i32]) -> (result: Vec<i32>)
    /* code modified by LLM (iteration 1): Fixed function structure by moving ensures clauses to proper position in function signature */
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
{
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    let mut result = Vec::new();
    let mut j = a.len();
    
    while j > 0
        invariant
            result.len() == a.len() - j,
            forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
        decreases j
    {
        j = j - 1;
        result.push(a[j]);
    }
    
    result
}

fn main() {}
}