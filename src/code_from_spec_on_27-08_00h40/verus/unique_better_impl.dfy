use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_strictly_increasing(v: &Vec<i32>) -> bool {
    forall|i: int, j: int|
        #![trigger v[i], v[j]]
        0 <= i && i < j && j < v.len() ==> v[i] < v[j]
}

spec fn is_non_decreasing(a: &[i32]) -> bool {
    forall|i: int, j: int|
        #![trigger a[i], a[j]]
        0 <= i && i < j && j < a.len() ==> a[i] <= a[j]
}

spec fn is_subsequence_of(result: &Vec<i32>, a: &[i32]) -> bool {
    forall|i: int| 0 <= i && i < result.len() ==> 
        exists|j: int| 0 <= j && j < a.len() && result[i] == a[j]
}
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
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|k: int| 0 <= k && k < result.len() ==> 
                exists|j: int| 0 <= j && j < i && result[k] == a[j],
            result.len() <= i,
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