use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    for i in 0..a.len()
        invariant
            i <= a.len(),
            i < a.len() ==> (result.len() == 0 || result@[(result.len() - 1) as int] <= a@[i as int]),
            forall|j: int, k: int| 0 <= j && j < k && k < result.len() ==> result@[j] < result@[k],
    {
        if result.is_empty() || a[i] > result[result.len() - 1] {
            result.push(a[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}