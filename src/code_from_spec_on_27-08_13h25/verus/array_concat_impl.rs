use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    
    i = 0;
    while i < b.len()
        invariant
            i <= b.len(),
            result.len() == a.len() + i,
            forall|j: int| 0 <= j && j < a.len() ==> result[j] == a[j],
            forall|j: int| 0 <= j && j < i ==> result[j + a.len()] == b[j],
        decreases b.len() - i
    {
        result.push(b[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}