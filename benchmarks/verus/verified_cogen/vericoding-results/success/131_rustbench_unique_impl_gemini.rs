// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): added explicit triggers to loop invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int, k: int| #![trigger result[j], result[k]] 0 <= j < k < result.len() ==> result[j] < result[k],
            forall|j: int| #![trigger result[j]] 0 <= j < result.len() ==> (exists|k: int| 0 <= k < i && result[j] == a[k]),
        decreases a.len() - i
    {
        let current_val = a[i];
        if result.len() == 0 {
            result.push(current_val);
        } else {
            let last_val = result[result.len() - 1];
            // From the invariant, we know `last_val` is some `a[k]` where `k < i`.
            // From the requires clause, we know `a` is sorted, so `a[k] <= a[i]`.
            // Therefore, `last_val <= current_val` must hold.
            if last_val < current_val {
                result.push(current_val);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}