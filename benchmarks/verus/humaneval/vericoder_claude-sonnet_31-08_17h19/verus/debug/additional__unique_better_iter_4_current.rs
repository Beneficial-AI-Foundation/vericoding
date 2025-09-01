use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|k: int|
                #![trigger result[k]]
                0 <= k && k < result.len() ==> exists|j: int| 0 <= j && j < i && result[k] == a[j],
            forall|k: int, l: int|
                #![trigger result[k], a[l]]
                0 <= k && k < result.len() && 0 <= l && l < i ==> 
                    exists|m: int| 0 <= m && m <= l && result[k] == a[m],
        decreases a.len() - i
    {
        if result.len() == 0 || a[i] > result[result.len() - 1] {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}