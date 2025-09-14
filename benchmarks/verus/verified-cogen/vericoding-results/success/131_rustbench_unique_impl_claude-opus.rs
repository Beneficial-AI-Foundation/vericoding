// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added trigger annotation to fix quantifier */
    let mut result = Vec::new();
    if a.len() == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    result.push(a[i]);
    i = i + 1;
    
    while i < a.len()
        invariant
            0 < i <= a.len(),
            result.len() > 0,
            result[result.len() - 1] == a[i - 1],
            forall|j: int, k: int|
                #![trigger result@[j], result@[k]]
                0 <= j && j < k && k < result.len() ==> result@[j] < result@[k],
            forall|j: int|
                #![trigger result@[j]]
                0 <= j && j < result.len() ==> exists|k: int| 0 <= k && k < i && result@[j] == a[k],
        decreases a.len() - i
    {
        if a[i] != result[result.len() - 1] {
            result.push(a[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}