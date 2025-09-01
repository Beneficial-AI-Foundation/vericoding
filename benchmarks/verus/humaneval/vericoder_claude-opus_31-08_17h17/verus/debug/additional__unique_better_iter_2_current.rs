use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a value exists in the result vector
spec fn contains_value(v: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i && i < v.len() && v[i] == val
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
            0 <= i <= a.len(),
            // Result is strictly increasing
            forall|j: int, k: int|
                #![trigger result@[j], result@[k]]
                0 <= j && j < k && k < result@.len() ==> result@[j] < result@[k],
            // All elements in result come from array a
            forall|j: int|
                #![trigger result@[j]]
                0 <= j && j < result@.len() ==> exists|k: int| 0 <= k && k < i as int && a[k as int] == result@[j],
            // If we have elements in result, the last one is less than any remaining elements in a
            result@.len() > 0 && i < a.len() ==> result@[result@.len() - 1] < a[i as int],
            // No duplicates from a[0..i] are missing from result
            forall|j: int|
                #![trigger a[j]]
                0 <= j && j < i as int ==> contains_value(result@, a[j]) || 
                    (exists|k: int| 0 <= k && k < j && a[k] == a[j])
    {
        // Check if current element is not a duplicate
        if result.len() == 0 || result[result.len() - 1] < a[i] {
            result.push(a[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}