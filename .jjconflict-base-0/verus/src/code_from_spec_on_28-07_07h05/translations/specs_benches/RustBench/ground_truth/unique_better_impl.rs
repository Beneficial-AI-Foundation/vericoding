use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    let mut result = Vec::new();
    
    if a.len() == 0 {
        return result;
    }
    
    result.push(a[0]);
    
    let mut i = 1;
    /* code modified by LLM (iteration 1): added trigger annotation for quantifier */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() > 0,
            result[result.len() - 1] == a[i - 1] || (exists|k: int| 0 <= k < i - 1 && result[result.len() - 1] == a[k] && forall|j: int| k < j < i ==> a[j] == a[k]),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
            forall|j: int| #![trigger result[j]] 0 <= j < result.len() ==> exists|k: int| 0 <= k < i && result[j] == a[k],
        decreases a.len() - i
    {
        if a[i] > result[result.len() - 1] {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}

fn main() {}
}