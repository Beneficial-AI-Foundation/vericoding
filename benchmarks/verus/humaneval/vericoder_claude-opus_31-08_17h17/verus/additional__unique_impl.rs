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
            result.len() > 0 ==> result[result.len() - 1] <= a[i as int - 1] || i == 0,
            forall|m: int| 
                #![trigger a[m]]
                0 <= m && m < i as int ==> 
                (exists|k: int| 0 <= k && k < result.len() && result[k] == a[m]) ||
                (exists|j: int| 0 <= j && j < m && a[j] == a[m]),
        decreases a.len() - i,
    {
        let old_result_len = result.len();
        
        if result.len() == 0 || result[result.len() - 1] < a[i as usize] {
            result.push(a[i as usize]);
            
            proof {
                // Prove that the new element maintains strict ordering
                if old_result_len > 0 {
                    assert(result[old_result_len - 1] < a[i as int]);
                    assert(result[old_result_len] == a[i as int]);
                }
                
                // Prove the invariants for the new state
                assert(forall|k: int| #![trigger result[k]] 0 <= k && k < old_result_len ==> 
                    exists|m: int| 0 <= m && m < i && a[m] == result[k]);
                assert(result[old_result_len] == a[i as int]);
            }
        } else {
            proof {
                // When we don't add the element, it must be a duplicate
                assert(result[result.len() - 1] >= a[i as int]);
                
                // Since the array is sorted and result contains unique elements < a[i],
                // a[i] must equal result[result.len() - 1]
                let last_idx = result.len() - 1;
                assert(exists|m: int| 0 <= m && m < i && a[m] == result[last_idx]);
                
                // This means a[i] is a duplicate of some earlier element
                assert(exists|j: int| 0 <= j && j < i && a[j] == a[i as int]);
            }
        }
        
        i = i + 1;
        
        proof {
            // Prove invariants hold after incrementing i
            assert(forall|m: int| 
                #![trigger a[m]]
                0 <= m && m < i - 1 ==> 
                (exists|k: int| 0 <= k && k < result.len() && result[k] == a[m]) ||
                (exists|j: int| 0 <= j && j < m && a[j] == a[m]));
                
            // Handle the case for a[i-1]
            if old_result_len < result.len() {
                assert(result[result.len() - 1] == a[i - 1]);
                assert(exists|k: int| 0 <= k && k < result.len() && result[k] == a[i - 1]);
            } else {
                assert(exists|j: int| 0 <= j && j < i - 1 && a[j] == a[i - 1]);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}