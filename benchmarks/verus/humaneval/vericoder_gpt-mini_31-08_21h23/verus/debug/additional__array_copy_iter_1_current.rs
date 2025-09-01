use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    // impl-start
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len();
        invariant result.len() == i;
        invariant forall |j: int| 0 <= j && j < i ==> result[j] == a[j];
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}