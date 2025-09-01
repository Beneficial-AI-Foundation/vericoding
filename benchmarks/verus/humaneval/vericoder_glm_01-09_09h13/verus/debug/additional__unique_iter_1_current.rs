use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper code needed for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
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
    if a.len() == 0 {
        return result;
    }
    result.push(a[0]);

    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 < result.len(),
            result.len() <= i,
            forall|j1: int, j2: int| 0 <= j1 < j2 < result.len() ==> result@[j1] < result@[j2],
            result[result.len()-1] <= a[i],
    {
        if a[i] > *result.last().unwrap() {
            result.push(a[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}