use vstd::prelude::*;

verus! {

//IMPL unique_better
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
        decreases a.len() - i
    {
        let current = a[i];
        
        /* code modified by LLM (iteration 4): Only add current element if it's different from the last element in result */
        if result.len() == 0 || current != result[result.len() - 1] {
            /* code modified by LLM (iteration 4): Added assertion to prove current > last element when result is non-empty */
            if result.len() > 0 {
                assert(current > result[result.len() - 1]);
            }
            result.push(current);
        }
        
        i = i + 1;
    }
    
    result
}

fn main() {}
}