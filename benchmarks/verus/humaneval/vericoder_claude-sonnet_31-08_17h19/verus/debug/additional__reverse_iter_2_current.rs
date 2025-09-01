use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[a.len() - 1 - j],
        decreases a.len() - i
    {
        result.push(a[a.len() - 1 - i]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}