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
    /* code modified by LLM (iteration 4): Added explicit type annotation to resolve type inference error */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): Enhanced loop invariants to maintain strict ordering property */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|j: int|
                #![trigger result[j]]
                0 <= j < result.len() ==> exists|k: int| 0 <= k < i && result[j] == a[k],
            result.len() > 0 ==> result[result.len() - 1] <= a[i - 1],
        decreases a.len() - i
    {
        /* code modified by LLM (iteration 4): Fixed type mismatch by casting i to int for array indexing */
        if result.len() == 0 || a[i as int] != result[result.len() - 1] {
            if result.len() > 0 {
                assert(a[i as int] >= result[result.len() - 1]);
                assert(a[i as int] != result[result.len() - 1]);
                assert(a[i as int] > result[result.len() - 1]);
            }
            result.push(a[i as int]);
        }
        i += 1;
    }
    
    result
}

fn main() {}
}