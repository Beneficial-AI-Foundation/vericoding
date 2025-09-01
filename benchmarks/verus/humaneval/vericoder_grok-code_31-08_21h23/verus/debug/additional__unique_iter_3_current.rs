use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_non_decreasing(a: Seq<i32>, idx: int)
    requires
        0 <= idx < a.len(),
        forall|p: int, q: int| #[trigger(a[p])] 0 <= p < q < a.len() ==> a[p] <= a[q],
    ensures
        forall|p: int| 0 <= p < idx + 1 ==> a[p] <= a[idx],
        forall|p: int| idx <= p < a.len() ==> a[idx] <= a[p],
{
    // Proof is handled by Verus automatically due to the precondition
}
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
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() > 0,
            forall|k: int| #[trigger(result@[k])] 0 <= k < (result.len() - 1) as int ==> result@[k] < result@[k + 1],
    {
        if a[i] != result[result.len() - 1] {
            let prev_len = result.len();
            assert(a[i] != result[prev_len - 1]);
            // From pre-condition, since i > 0 and a is non-decreasing, a[i] >= a[prev_indices]
            // In particular, a[i] > a[j] for j < i where a[j] <= a[i]
            // We only push if a[i] != last, and since last is some a[j] <= a[i], if != then >
            // This ensures result remains strictly increasing
            result.push(a[i]);
            // Assert the new element is greater than the previous
            if prev_len > 0 {
                assert(result@[prev_len - 1] < result@[prev_len]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}