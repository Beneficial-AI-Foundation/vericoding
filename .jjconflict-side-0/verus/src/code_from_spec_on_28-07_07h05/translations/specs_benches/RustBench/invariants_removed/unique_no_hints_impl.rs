use vstd::prelude::*;

verus! {

//IMPL unique
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    /* code modified by LLM (iteration 4): Completely restructured to ensure strict ordering invariant */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            /* code modified by LLM (iteration 4): Added explicit triggers for the quantifier */
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 
                #![trigger result[k], a[j]]
                0 <= j < i && result[k] == a[j],
        decreases a.len() - i
    {
        let current = a[i as usize];
        
        /* code modified by LLM (iteration 4): Only add element if it's strictly greater than last element or if result is empty */
        if result.len() == 0 || current > result[result.len() - 1] {
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}

fn main() {}
}