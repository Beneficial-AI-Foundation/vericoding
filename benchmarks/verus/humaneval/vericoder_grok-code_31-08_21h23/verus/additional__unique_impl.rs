use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_non_decreasing(a: Seq<i32>, idx: int)
    requires
        0 <= idx < a.len(),
        forall|p: int, q: int| 
            #![trigger(a[p])]
            0 <= p < q < a.len() ==> a[p] <= a[q],
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
    let mut i: int = 1;
    while i < (a.len() as int)
        invariant
            i <= (a.len() as int),
            result.len > 0,
            forall|k: int| 
                #![trigger(result@[k], result@[k + 1])]
                0 <= k < ((result.len as int) - 1) ==> result@[k] < result@[k + 1],
    {
        if a[(i as usize)] != result@[((result.len as int) - 1)] {
            let prev_len = result.len as int;
            result.push(a[(i as usize)]);
            if prev_len > 0 {
                assert(result@[prev_len - 1] < result@[(prev_len)]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}