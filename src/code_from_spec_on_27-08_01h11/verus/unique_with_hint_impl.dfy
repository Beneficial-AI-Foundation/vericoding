use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(v: &Vec<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && v@[i] == val
}

spec fn all_values_from_array(result: &Vec<i32>, a: &[i32]) -> bool {
    forall|i: int| 0 <= i < result.len() ==> contains_value_in_slice(a, result@[i])
}

spec fn contains_value_in_slice(a: &[i32], val: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == val
}

spec fn all_unique_values_included(a: &[i32], result: &Vec<i32>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> 
        (forall|j: int| 0 <= j < i && a[j] == a[i]) || contains_value(result, a[i])
}
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
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|k: int| 
                #![trigger result@[k]]
                0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && a[j] == result@[k],
            forall|j: int| 
                #![trigger a[j]]
                0 <= j < i ==> 
                (exists|k: int| 0 <= k < j && a[k] == a[j]) || 
                (exists|k: int| 0 <= k < result.len() && result@[k] == a[j]),
        decreases a.len() - i
    {
        let mut found = false;
        let mut j = 0;
        
        while j < i
            invariant
                0 <= j <= i,
                found == exists|k: int| 0 <= k < j && a[k] == a[i as int],
            decreases i - j
        {
            if a[j] == a[i] {
                found = true;
            }
            j += 1;
        }
        
        if !found {
            result.push(a[i]);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}