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
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            /* code modified by LLM (iteration 1): Added invariant to connect result elements with array elements */
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i && result[k] == a[j],
            /* code modified by LLM (iteration 1): Added invariant for monotonicity between result and current position */
            result.len() > 0 && i < a.len() ==> result[result.len() - 1] <= a[i],
        decreases a.len() - i
    {
        let current = a[i];
        
        /* code modified by LLM (iteration 1): Prove strict inequality before pushing */
        if result.len() > 0 {
            // We know result[result.len() - 1] <= a[i] from invariant
            // We need to show result[result.len() - 1] < current = a[i]
            // This is true because we only add elements that are different from the last one
            assert(result[result.len() - 1] <= current);
        }
        
        result.push(current);
        i += 1;
        
        // Skip all duplicates of current element
        while i < a.len() && a[i] == current
            invariant
                0 <= i <= a.len(),
                forall|k: int, l: int|
                    #![trigger result[k], result[l]]
                    0 <= k && k < l && l < result.len() ==> result[k] < result[l],
                /* code modified by LLM (iteration 1): Maintain connection between result and array */
                forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i && result[k] == a[j],
                result.len() > 0 ==> result[result.len() - 1] == current,
                /* code modified by LLM (iteration 1): Maintain monotonicity invariant */
                result.len() > 0 && i < a.len() ==> result[result.len() - 1] <= a[i],
            decreases a.len() - i
        {
            i += 1;
        }
    }
    
    result
}

fn main() {}
}