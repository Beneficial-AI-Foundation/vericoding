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
    /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|k: int|
                #![trigger result[k]]
                0 <= k && k < result.len() ==> exists|j: int| 0 <= j && j < i && result[k] == a[j],
        decreases a.len() - i
    {
        if result.len() == 0 || result[result.len() - 1] != a[i] {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}