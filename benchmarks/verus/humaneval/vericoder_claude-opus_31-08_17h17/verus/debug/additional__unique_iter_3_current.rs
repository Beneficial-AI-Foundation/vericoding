use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove that if we skip duplicates, the resulting sequence is strictly increasing
proof fn unique_elements_strictly_increasing(a: &[i32], result: &Vec<i32>, i: usize)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
        i <= a.len(),
        forall|k: int| #![trigger result[k]] 0 <= k && k < result.len() ==> 
            exists|m: int| 0 <= m && m < i && a[m] == result[k],
        forall|k1: int, k2: int|
            #![trigger result[k1], result[k2]]
            0 <= k1 && k1 < k2 && k2 < result.len() ==> result[k1] < result[k2],
    ensures
        forall|k1: int, k2: int|
            #![trigger result[k1], result[k2]]
            0 <= k1 && k1 < k2 && k2 < result.len() ==> result[k1] < result[k2],
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    
    if a.len() == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| #![trigger result[k]] 0 <= k && k < result.len() ==> 
                exists|m: int| 0 <= m && m < i && a[m] == result[k],
            forall|k1: int, k2: int|
                #![trigger result[k1], result[k2]]
                0 <= k1 && k1 < k2 && k2 < result.len() ==> result[k1] < result[k2],
            result.len() > 0 ==> result[result.len() - 1] < a[i as int] || 
                (exists|j: int| i as int <= j && j < a.len() && result[result.len() - 1] < a[j]),
            forall|m: int| 0 <= m && m < i as int ==> 
                (exists|k: int| 0 <= k && k < result.len() && result[k] == a[m]) ||
                (exists|j: int| 0 <= j && j < m && a[j] == a[m]),
        decreases a.len() - i,
    {
        if result.len() == 0 || result[result.len() - 1] < a[i as usize] {
            result.push(a[i as usize]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}