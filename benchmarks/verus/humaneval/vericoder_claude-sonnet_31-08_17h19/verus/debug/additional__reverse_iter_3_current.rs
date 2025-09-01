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
        let idx = a.len() - 1 - i;
        assert(0 <= idx && idx < a.len());
        result.push(a[idx]);
        i += 1;
    }
    
    assert(result.len() == a.len());
    assert(forall|j: int| 0 <= j && j < result.len() ==> result[j] == a[a.len() - 1 - j]);
    
    result
}
// </vc-code>

fn main() {}
}