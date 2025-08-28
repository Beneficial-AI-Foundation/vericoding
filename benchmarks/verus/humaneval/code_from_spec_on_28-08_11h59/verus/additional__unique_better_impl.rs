use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_sorted_non_decreasing(a: &[i32]) -> bool {
    forall|i: int, j: int| 
        #![trigger a[i], a[j]]
        0 <= i && i < j && j < a.len() ==> a[i] <= a[j]
}

spec fn is_sorted_strictly_increasing(v: &Vec<i32>) -> bool {
    forall|i: int, j: int| 
        #![trigger v[i], v[j]]
        0 <= i && i < j && j < v.len() ==> v[i] < v[j]
}

spec fn is_subsequence(result: &Vec<i32>, a: &[i32]) -> bool {
    forall|i: int| 
        #![trigger result[i]]
        0 <= i && i < result.len() ==> exists|j: int| 0 <= j && j < a.len() && result[i] == a[j]
}

spec fn contains_all_unique(result: &Vec<i32>, a: &[i32]) -> bool {
    forall|i: int| 
        #![trigger a[i]]
        0 <= i && i < a.len() ==> 
        (forall|j: int| 0 <= j && j < i ==> a[j] != a[i]) ==> 
        exists|k: int| 0 <= k && k < result.len() && result[k] == a[i]
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
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            is_sorted_strictly_increasing(&result),
            forall|k: int| 
                #![trigger result[k]]
                0 <= k && k < result.len() ==> 
                exists|j: int| 0 <= j && j < i && result[k] == a[j],
            forall|j: int| 
                #![trigger a[j]]
                0 <= j && j < i ==> 
                (forall|k: int| 0 <= k && k < j ==> a[k] != a[j]) ==> 
                exists|m: int| 0 <= m && m < result.len() && result[m] == a[j],
            forall|k1: int, k2: int| 
                #![trigger result[k1], result[k2]]
                0 <= k1 && k1 < k2 && k2 < result.len() ==> result[k1] != result[k2]
        decreases a.len() - i
    {
        let current = a[i];
        let mut should_add = true;
        
        if result.len() > 0 && result[result.len() - 1] == current {
            should_add = false;
        }
        
        if should_add {
            result.push(current);
            proof {
                assert(forall|j: int| 
                    #![trigger a[j]]
                    0 <= j && j < i + 1 ==> 
                    (forall|k: int| 0 <= k && k < j ==> a[k] != a[j]) ==> 
                    exists|m: int| 0 <= m && m < result.len() && result[m] == a[j]);
            }
        } else {
            proof {
                assert(current == result[result.len() - 1]);
                assert(exists|prev_j: int| 0 <= prev_j && prev_j < i && 
                       a[prev_j] == current &&
                       (forall|k: int| 0 <= k && k < prev_j ==> a[k] != a[prev_j]));
                assert(forall|k: int| 0 <= k && k < i ==> a[k] != current);
                assert(forall|j: int| 
                    #![trigger a[j]]
                    0 <= j && j < i + 1 ==> 
                    (forall|k: int| 0 <= k && k < j ==> a[k] != a[j]) ==> 
                    exists|m: int| 0 <= m && m < result.len() && result[m] == a[j]);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}