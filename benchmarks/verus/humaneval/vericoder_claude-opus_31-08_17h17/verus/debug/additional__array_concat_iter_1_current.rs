use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = a.clone();
    let mut i: usize = 0;
    
    while i < b.len()
        invariant
            i <= b.len(),
            result.len() == a.len() + i,
            forall|j: int| 0 <= j && j < a.len() ==> result[j] == a[j],
            forall|j: int| 0 <= j && j < i ==> result[a.len() + j] == b[j],
    {
        result.push(b[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}