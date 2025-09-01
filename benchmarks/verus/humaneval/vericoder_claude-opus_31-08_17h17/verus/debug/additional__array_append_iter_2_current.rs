use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    // Copy all elements from a
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j && j < i ==> result[j] == a[j],
        decreases
            a.len() - i,
    {
        result.push(a[i]);
        i = i + 1;
    }
    
    // Append b at the end
    result.push(b);
    
    // Verify the postconditions are met
    assert(result.len() == a.len() + 1);
    assert(forall|k: int| #![auto] 0 <= k && k < result.len() ==> 
        result[k] == (if k < a.len() { a[k] } else { b }));
    
    result
}
// </vc-code>

fn main() {}
}