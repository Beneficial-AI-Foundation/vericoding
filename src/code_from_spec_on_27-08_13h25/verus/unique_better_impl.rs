use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
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
    if a.len() == 0 {
        return result;
    }

    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |k: int, l: int| 0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            result.len() > 0 ==> result[result.len() - 1] <= a[if i > 0 { (i - 1) as int } else { 0 }],
        decreases a.len() - i,
    {
        if i == 0 || (result.len() > 0 && a[i] > result[result.len() - 1]) {
            result.push(a[i]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {}
}