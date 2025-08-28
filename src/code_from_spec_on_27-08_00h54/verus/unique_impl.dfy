use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(v: &Vec<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == val
}

spec fn all_from_input(result: &Vec<i32>, a: &[i32]) -> bool {
    forall|i: int| 0 <= i < result.len() ==> contains_value_slice(a, result[i])
}

spec fn contains_value_slice(a: &[i32], val: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == val
}

spec fn all_unique_values(result: &Vec<i32>, a: &[i32]) -> bool {
    forall|val: i32| contains_value_slice(a, val) ==> contains_value(result, val)
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
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|k: int|
                0 <= k < result.len() ==> exists|j: int| 0 <= j < i && a[j] == result[k],
            forall|j: int|
                0 <= j < i ==> (exists|k: int| 0 <= k < result.len() && result[k] == a[j]),
    {
        let current = a[i];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}