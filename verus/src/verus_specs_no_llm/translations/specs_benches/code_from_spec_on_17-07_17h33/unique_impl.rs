use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    /* code modified by LLM (iteration 1): Fixed function signature - moved requires/ensures clauses inside function body */
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    /* code modified by LLM (iteration 3): Added explicit type annotation to Vec::new() to fix compilation error */
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|x: int, y: int|
                #![trigger result[x], result[y]]
                0 <= x && x < y && y < result.len() ==> result[x] < result[y],
            forall|k: int|
                0 <= k && k < result.len() ==> exists|j: int| 0 <= j && j < a.len() && result[k] == a[j],
    {
        /* code modified by LLM (iteration 2): Fixed type casting - removed 'as int' casts which are not allowed in executable code */
        if result.len() == 0 || a[i] > result[result.len() - 1] {
            result.push(a[i]);
        }
    }
    
    result
}

fn main() {}
}