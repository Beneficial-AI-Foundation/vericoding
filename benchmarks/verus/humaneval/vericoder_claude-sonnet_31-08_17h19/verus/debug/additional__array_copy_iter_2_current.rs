use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
        decreases a.len() - i,
    {
        result.push(a[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}