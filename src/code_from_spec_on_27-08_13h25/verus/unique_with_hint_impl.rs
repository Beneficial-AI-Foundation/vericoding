use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    if a.len() == 0 {
        return result;
    }

    let mut i: usize = 0;
    result.push(a[0]);

    while i < a.len() - 1
        invariant
            0 <= i && i < a.len(),
            result.len() > 0,
            forall|k: int, l: int|
                #![trigger result[k], result[l]]
                0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            forall|k: int|
                #![trigger result[k]]
                0 <= k && k < result.len() ==> exists|m: int| 0 <= m && m <= i && result[k] == a[m],
            result[result.len() - 1] == a[i as int],
        decreases a.len() - i
    {
        i = i + 1;
        if a[i] > result[result.len() - 1] {
            result.push(a[i]);
        }
    }

    result
}
// </vc-code>

fn main() {}
}