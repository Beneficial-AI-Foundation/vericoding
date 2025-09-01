use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
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
    for i: usize in 0..a.len() {
        invariant
            result.len() == i,
            forall|j: usize| 0 <= j && j < i ==> result[j] == a[j]
        result.push(a[i]);
    }
    result
}
// </vc-code>

fn main() {}
}