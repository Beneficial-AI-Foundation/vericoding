use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Vec::new();
    if a.is_empty() {
        return result;
    }
    result.push(a[0]);
    for i in 1..a.len() {
        loop invariant (
            result.len() >= 1 &&
            forall |j: int| 
                #![trigger result[j]]
                #![trigger result[j+1]]
                (0 <= j && j < result.len()-1) ==> result[j] < result[j+1]
        );
        if a[i] > result[result.len()-1] {
            result.push(a[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}