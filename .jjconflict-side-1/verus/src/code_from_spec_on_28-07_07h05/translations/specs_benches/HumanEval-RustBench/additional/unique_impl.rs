use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
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
        result.push(current);
        
        /* code modified by LLM (iteration 1): Fixed invariants to properly handle loop conditions and ordering */
        // Skip all duplicates
        while i < a.len() && a[i] == current
            invariant
                0 <= i <= a.len(),
                /* code modified by LLM (iteration 1): Simplified condition - when loop exits, either i == a.len() or a[i] != current */
                i < a.len() ==> a[i] == current,
                forall|k: int, l: int|
                    #![trigger result[k], result[l]]
                    0 <= k && k < l && l < result.len() ==> result[k] < result[l],
                /* code modified by LLM (iteration 1): Maintain that current is the last element added */
                result.len() > 0,
                result[result.len() - 1] == current,
                /* code modified by LLM (iteration 1): Ensure all previous elements are less than current */
                forall|k: int| 0 <= k < result.len() - 1 ==> result[k] < current,
            decreases a.len() - i
        {
            i += 1;
        }
    }
    
    result
}

fn main() {}
}