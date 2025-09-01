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
    if a.is_empty() {
        vec![]
    } else {
        let mut result = Vec::new();
        result.push(a[0]);
        for i in 1..a.len() {
            invariant
                result.len() >= 1
                && (forall |k: int| #[trigger result[k]] #[trigger result[k+1]] 0 <= k && k < result.len()-1 ==> result[k] < result[k+1])
                && (i > 0 ==> result[result.len()-1] <= a[i-1])
                && i <= a.len()
            if a[i] > a[i-1] {
                result.push(a[i]);
            }
        }
        result
    }
}
// </vc-code>

fn main() {}
}